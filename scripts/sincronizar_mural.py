"""Coletor horário delegado à titular. Executar fora do processo web do Gestor."""
import base64
import hashlib
import io
import json
import os
import sys
from datetime import datetime, timedelta, timezone
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import quote, urlsplit

import openpyxl
import requests

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from mural_log import diferencas_planilha, fontes_ausentes, horario, snapshot_planilha

GRAPH = 'https://graph.microsoft.com/v1.0'


class Texto(HTMLParser):
    def __init__(self):
        super().__init__()
        self.partes, self.links = [], []

    def handle_data(self, texto):
        self.partes.append(texto)

    def handle_starttag(self, tag, attrs):
        if tag in {'br', 'p', 'div', 'li'}:
            self.partes.append('\n')
        if tag == 'a':
            self.links.extend(v for k, v in attrs if k == 'href' and v)


def agora():
    return datetime.now(timezone.utc).isoformat()


class Graph:
    def __init__(self, token):
        self.sessao = requests.Session()
        self.sessao.headers['Authorization'] = f'Bearer {token}'

    def get(self, caminho):
        url = caminho if caminho.startswith('https://') else GRAPH + caminho
        if not url.startswith(GRAPH + '/'):
            raise ValueError('Paginação fora do Microsoft Graph.')
        resposta = self.sessao.get(url, timeout=40, allow_redirects=False)
        resposta.raise_for_status()
        return resposta.json()

    def lista(self, caminho):
        for _ in range(1000):
            pagina = self.get(caminho)
            yield from pagina.get('value', [])
            caminho = pagina.get('@odata.nextLink')
            if not caminho:
                return
        raise ValueError('Limite de paginação atingido; cursor preservado para nova tentativa.')

    def arquivo(self, caminho):
        resposta = self.sessao.get(GRAPH + caminho + '/content', timeout=40, allow_redirects=False)
        if resposta.status_code in (301, 302, 303, 307, 308):
            url = resposta.headers['Location']
            if urlsplit(url).scheme != 'https':
                raise ValueError('Download inseguro.')
            # URL temporária já é autenticada: nunca encaminhar o Bearer do Graph.
            resposta = requests.get(url, timeout=60, stream=True)
        resposta.raise_for_status()
        partes, tamanho = [], 0
        for parte in resposta.iter_content(65536):
            tamanho += len(parte)
            if tamanho > 24 * 1024 * 1024:
                raise ValueError('Planilha excedeu o limite de download.')
            partes.append(parte)
        return b''.join(partes)


def token_delegado():
    tenant = os.environ['MS_GRAPH_TENANT_ID']
    if not tenant or any(c not in '0123456789abcdefABCDEF-' for c in tenant):
        raise ValueError('Tenant inválido.')
    resposta = requests.post(f'https://login.microsoftonline.com/{tenant}/oauth2/v2.0/token',
        data={'grant_type': 'refresh_token', 'client_id': os.environ['MS_GRAPH_CLIENT_ID'],
              'client_secret': os.environ['MS_GRAPH_CLIENT_SECRET'],
              'refresh_token': os.environ['MS_GRAPH_REFRESH_TOKEN']}, timeout=40)
    resposta.raise_for_status()
    return resposta.json()['access_token']


def evento_mensagem(msg, contexto, desde):
    quando = msg.get('lastModifiedDateTime') or msg.get('createdDateTime')
    if not quando or horario(quando) < horario(desde) or msg.get('messageType') != 'message':
        return None, []
    parser = Texto()
    parser.feed((msg.get('body') or {}).get('content') or '')
    arquivos = msg.get('attachments') or []
    links = parser.links + [a['contentUrl'] for a in arquivos if a.get('contentUrl')]
    corpo = ''.join(parser.partes).strip()
    if arquivos:
        corpo += '\nArquivos: ' + ', '.join(a.get('name') or 'Anexo' for a in arquivos)
    acao = 'Mensagem nova'
    if msg.get('deletedDateTime'):
        acao, corpo = 'Mensagem excluída', 'O conteúdo da mensagem foi excluído no Teams.'
    elif msg.get('lastEditedDateTime'):
        acao = 'Mensagem editada'
    if not corpo:
        return None, links
    autor = ((msg.get('from') or {}).get('user') or {}).get('displayName') or 'Autor não informado'
    assinatura = hashlib.sha256(json.dumps([corpo, acao], ensure_ascii=False).encode()).hexdigest()
    return dict(contexto, chave=f"{contexto['id']}:{msg['id']}:{quando}:{assinatura}",
                ocorrido_em=quando, autor=autor, texto=f'{acao}\n{corpo}'[:12000],
                link=msg.get('webUrl') or contexto.get('link', '')), links


def link_planilha(url):
    partes = urlsplit(url)
    host = (partes.hostname or '').lower()
    return (partes.scheme == 'https' and host.endswith('.sharepoint.com')
            and ('.xlsx' in partes.path.lower() or '/:x:/' in partes.path.lower()))


def executar():
    destino = os.environ['GESTOR_URL'].rstrip('/') + '/api/mural/sincronizacao'
    if urlsplit(destino).scheme != 'https':
        raise ValueError('O Gestor precisa usar HTTPS.')
    ponte = requests.Session()
    ponte.headers['Authorization'] = 'Bearer ' + os.environ['MURAL_SYNC_SECRET']
    resposta = ponte.get(destino, timeout=60)
    resposta.raise_for_status()
    estados = resposta.json()['estados']
    dono = os.environ['MS_GRAPH_USER_ID']
    eventos, novos_estados, falhas = [], {}, []
    inicio, fontes = agora(), 0
    esperadas = json.loads(os.environ.get('MURAL_EXPECTED_SOURCES_JSON', '[]'))
    encontradas = set()
    referencia = os.environ.get('MURAL_SYNC_START') or (datetime.now(timezone.utc) - timedelta(hours=1)).isoformat()
    graph = Graph(token_delegado())
    if graph.get('/me')['id'] != dono:
        raise ValueError('A conta Microsoft conectada difere da titular configurada.')
    planilhas = {p['id']: p for p in estados.get('planilhas_descobertas', [])}
    for p in json.loads(os.environ.get('MURAL_SPREADSHEETS_JSON', '[]')):
        identidade = p.get('id') or f"{p['drive_id']}:{p['item_id']}"
        planilhas[identidade] = dict(p, id=identidade)

    def descobrir(links):
        for url in links:
            if link_planilha(url):
                identidade = hashlib.sha256(url.encode()).hexdigest()
                planilhas.setdefault(identidade, dict(id=identidade, url=url))

    def ler_fonte(chave, contexto, caminho, canal=False):
        nonlocal fontes
        desde = estados.get(chave, {}).get('desde', referencia)
        locais, links = [], []
        if not canal:
            filtro = quote(f'lastModifiedDateTime gt {desde}', safe='')
            caminho += f'?$top=50&$orderby=lastModifiedDateTime desc&$filter={filtro}'
        else:
            caminho += '?$top=50&$expand=replies'
        for msg in graph.lista(caminho):
            ev, encontrados = evento_mensagem(msg, contexto, desde)
            if ev:
                locais.append(ev)
            links.extend(encontrados)
            if canal:
                # A ordenação considera toda a cadeia de respostas, não apenas a raiz.
                for reply in msg.get('replies', []):
                    ev, encontrados = evento_mensagem(reply, contexto, desde)
                    if ev:
                        locais.append(ev)
                    links.extend(encontrados)
                if msg.get('replies@odata.nextLink'):
                    for reply in graph.lista(msg['replies@odata.nextLink']):
                        ev, encontrados = evento_mensagem(reply, contexto, desde)
                        if ev:
                            locais.append(ev)
                        links.extend(encontrados)
        eventos.extend(locais)
        descobrir(links)
        novos_estados[chave] = {'desde': inicio}
        fontes += 1

    try:
        for chat in graph.lista('/me/chats?$top=50'):
            if chat.get('chatType') not in {'group', 'meeting'}:
                continue  # Nem ler mensagens de chats entre duas pessoas.
            cid = quote(chat['id'], safe='')
            try:
                membros = {m.get('userId') for m in graph.lista(f'/chats/{cid}/members') if m.get('userId')}
                if len(membros) < 3 or dono not in membros:
                    continue
                encontradas.add(('grupo', chat['id']))
                contexto = dict(fonte='teams_grupo', id=chat['id'], membros=sorted(membros),
                                tipo_chat=chat['chatType'], origem=chat.get('topic') or 'Grupo do Teams',
                                link=chat.get('webUrl', ''))
                ler_fonte('chat:' + chat['id'], contexto, f'/chats/{cid}/messages')
            except (requests.RequestException, ValueError, KeyError):
                falhas.append('Grupo: ' + (chat.get('topic') or chat['id']))
    except requests.RequestException:
        falhas.append('Não foi possível listar os grupos da titular.')

    try:
        for team in graph.lista('/me/joinedTeams'):
            encontradas.add(('equipe', team['id']))
            tid = quote(team['id'], safe='')
            try:
                for canal in graph.lista(f'/teams/{tid}/channels'):
                    cid = quote(canal['id'], safe='')
                    nome = f"{team.get('displayName', 'Equipe')} / {canal.get('displayName', 'Canal')}"
                    try:
                        if canal.get('membershipType') != 'standard':
                            membros = {m.get('userId') for m in graph.lista(f'/teams/{tid}/channels/{cid}/members')}
                            if dono not in membros:
                                continue
                        contexto = dict(fonte='teams_canal', id=canal['id'], origem=nome,
                                        membro_confirmado=True, link=canal.get('webUrl', ''))
                        ler_fonte('canal:' + canal['id'], contexto, f'/teams/{tid}/channels/{cid}/messages', True)
                    except (requests.RequestException, ValueError, KeyError):
                        falhas.append('Canal: ' + nome)
            except requests.RequestException:
                falhas.append('Canais da equipe: ' + team.get('displayName', team['id']))
    except requests.RequestException:
        falhas.append('Não foi possível listar as equipes da titular.')

    for identidade, config in planilhas.items():
        try:
            if config.get('url'):
                share = 'u!' + base64.urlsafe_b64encode(config['url'].encode()).decode().rstrip('=')
                item = graph.get('/shares/' + share + '/driveItem')
                caminho = f"/drives/{quote(item['parentReference']['driveId'], safe='')}/items/{quote(item['id'], safe='')}"
            else:
                caminho = f"/drives/{quote(config['drive_id'], safe='')}/items/{quote(config['item_id'], safe='')}"
                item = graph.get(caminho)
            chave = 'arquivo:' + hashlib.sha256(caminho.encode()).hexdigest()
            anterior = estados.get(chave)
            versao = item.get('cTag') or item.get('eTag')
            if anterior and versao and anterior.get('versao') == versao:
                fontes += 1
                continue
            workbook = openpyxl.load_workbook(io.BytesIO(graph.arquivo(caminho)), read_only=True, data_only=False)
            try:
                atual = snapshot_planilha(workbook)
            finally:
                workbook.close()
            mudancas = diferencas_planilha(anterior.get('abas') if anterior else None, atual)
            if mudancas:
                # Metadados do arquivo não atribuem cada célula a uma pessoa.
                ultimo_editor = ((item.get('lastModifiedBy') or {}).get('user') or {}).get('displayName')
                texto = '\n'.join(mudancas)
                if ultimo_editor:
                    texto += '\nÚltimo editor do arquivo informado pela Microsoft: ' + ultimo_editor
                assinatura = hashlib.sha256(json.dumps(atual, sort_keys=True).encode()).hexdigest()
                eventos.append(dict(fonte='planilha', chave=f'{chave}:{versao}:{assinatura}',
                                    autor='Alteração na planilha', origem=item.get('name') or config.get('nome') or 'Planilha',
                                    texto=texto[:12000], link=item.get('webUrl', ''),
                                    ocorrido_em=item.get('lastModifiedDateTime') or inicio))
            novos_estados[chave] = {'versao': versao, 'abas': atual}
            fontes += 1
        except Exception:
            # Não avançar o estado desta fonte; tentar novamente na próxima execução.
            falhas.append('Planilha: ' + (config.get('nome') or identidade))
    falhas.extend(fontes_ausentes(esperadas, encontradas))
    novos_estados['planilhas_descobertas'] = list(planilhas.values())
    novos_estados['saude'] = dict(verificado_em=inicio, fontes_verificadas=fontes, falhas=falhas)
    # Só confirmar os cursores depois que todos os eventos chegaram ao Gestor.
    for posicao in range(0, len(eventos), 500):
        resposta = ponte.post(destino, json={'dono': dono, 'eventos': eventos[posicao:posicao + 500]}, timeout=90)
        resposta.raise_for_status()
    resposta = ponte.post(destino, json={'dono': dono, 'estados': novos_estados}, timeout=90)
    resposta.raise_for_status()
    print(f'{fontes} fontes verificadas; {len(eventos)} eventos enviados; {len(falhas)} fontes com falha.')
    if falhas:
        raise RuntimeError('Sincronização parcial. Consulte as fontes pendentes no log do mural.')


if __name__ == '__main__':
    try:
        executar()
    except Exception as erro:
        # Não imprimir resposta OAuth, tokens, URLs temporárias ou conteúdo das mensagens.
        print(f'Falha na sincronização ({type(erro).__name__}). Confira a configuração e o log do mural.', file=sys.stderr)
        sys.exit(1)
