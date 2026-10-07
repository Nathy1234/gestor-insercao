"""Log de equipe: contratos de entrada e comparação de planilhas, sem rede."""
import hashlib
import json
from datetime import datetime, timezone
from urllib.parse import urlsplit

def horario(valor):
    dt = datetime.fromisoformat(str(valor).replace('Z', '+00:00'))
    if dt.tzinfo is None:
        raise ValueError('Horário precisa ter fuso.')
    return dt.astimezone(timezone.utc).replace(tzinfo=None)


def link_seguro(valor):
    partes = urlsplit(valor or '')
    host = (partes.hostname or '').lower()
    if partes.scheme != 'https' or partes.username or partes.password:
        return ''
    if host in {'teams.microsoft.com', 'teams.cloud.microsoft'} or host.endswith('.sharepoint.com'):
        return valor
    return ''


def validar_evento(evento, dono):
    """A ponte autenticada precisa provar o escopo antes de gravar conteúdo."""
    if not isinstance(evento, dict):
        raise ValueError('Evento inválido.')
    fonte = evento.get('fonte')
    if fonte not in {'teams_grupo', 'teams_canal', 'planilha'}:
        raise ValueError('Fonte inválida.')
    if fonte == 'teams_grupo':
        membros = set(evento.get('membros') or [])
        if evento.get('tipo_chat') not in {'group', 'meeting'} or len(membros) < 3 or dono not in membros:
            raise ValueError('Conversas entre duas pessoas e grupos sem a titular ficam fora do log.')
    if fonte == 'teams_canal' and evento.get('membro_confirmado') is not True:
        raise ValueError('Canal sem acesso confirmado.')
    identidade = str(evento.get('chave') or '')
    if not identidade or len(identidade) > 2000:
        raise ValueError('Identidade inválida.')
    texto = str(evento.get('texto') or '').strip()
    if not texto or len(texto) > 12000:
        raise ValueError('Texto inválido.')
    return dict(chave=hashlib.sha256((fonte + ':' + identidade).encode()).hexdigest(),
                fonte=fonte, autor=str(evento.get('autor') or 'Não informado')[:200],
                origem=str(evento.get('origem') or '')[:300], texto=texto,
                link=link_seguro(str(evento.get('link') or '')),
                ocorrido_em=horario(evento['ocorrido_em']))


def snapshot_planilha(workbook):
    """Todas as abas, incluindo ocultas. Guardamos hashes, nunca valores das células."""
    resultado = {}
    total = 0
    for aba in workbook.worksheets:
        celulas = {}
        for linha in aba.iter_rows():
            for celula in linha:
                if celula.value is None:
                    continue
                total += 1
                if total > 250000:
                    raise ValueError('Planilha excedeu o limite de 250 mil células preenchidas.')
                valor = json.dumps([celula.data_type, str(celula.value)], ensure_ascii=False)
                celulas[celula.coordinate] = hashlib.sha256(valor.encode()).hexdigest()
        resultado[aba.title] = celulas
    return resultado


def diferencas_planilha(antes, depois):
    if antes is None:
        return []  # Primeira leitura cria a referência; não inventa alterações anteriores.
    resultado = []
    for aba in sorted(set(antes) | set(depois)):
        if aba not in antes:
            resultado.append(f'Aba adicionada: {aba} ({len(depois[aba])} células preenchidas).')
        elif aba not in depois:
            resultado.append(f'Aba removida: {aba}.')
        else:
            antigo, novo = antes[aba], depois[aba]
            mudaram = sorted(c for c in set(antigo) | set(novo) if antigo.get(c) != novo.get(c))
            if mudaram:
                amostra = ', '.join(mudaram[:30])
                resto = f' e outras {len(mudaram) - 30}' if len(mudaram) > 30 else ''
                resultado.append(f'{aba}: {len(mudaram)} células alteradas ({amostra}{resto}).')
    return resultado


def fontes_ausentes(esperadas, encontradas):
    """Fontes fornecidas pela titular não podem sumir silenciosamente da descoberta."""
    return [f"Fonte configurada não encontrada: {f.get('nome') or f['id']}"
            for f in esperadas if (f['tipo'], f['id']) not in encontradas]
