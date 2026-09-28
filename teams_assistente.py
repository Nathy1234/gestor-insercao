"""Leitura conservadora de publicações e respostas do canal Inserção de Materiais.

Recebe mensagens normalizadas do Graph. Não altera calendário nem envia mensagens.
"""
from collections import defaultdict
from datetime import datetime, timezone
from zoneinfo import ZoneInfo
import re
import unicodedata


EQUIPE = {
    '4bb6c1cd-16b8-4a6b-b380-cb7b514a2482',  # Lucas
    'a1eabea9-d48f-4462-a014-a97c692519e3',  # Stéfanye
    '5e0f4fa9-bf34-4dce-a5ef-4ebbc80f3767',  # Pedro
    '2a60721d-4b23-4fc3-bf53-497cf5efe34c',  # Everson
}
FUSO = ZoneInfo('America/Sao_Paulo')


def _normalizar(valor):
    sem_acentos = ''.join(c for c in unicodedata.normalize('NFKD', valor or '')
                         if not unicodedata.combining(c))
    return re.sub(r'\s+', ' ', sem_acentos.lower())


def _marcadores(texto):
    blocos = [_normalizar(b) for b in re.split(r'[.!?;\n]+', texto or '')]
    texto = _normalizar(texto)
    acao = bool(re.search(r'\b(inserid[oa]s?|atualizad[oa]s?|finalizad[oa]s?|concluid[oa]s?|'
                          r'corrigid[oa]s?|ajustad[oa]s?|realizad[oa]s?)\b', texto))
    if re.search(r'\b(nao|ainda nao|sem)\s+(?:foi\s+)?(?:inserid|finalizad|concluid|atualizad)', texto):
        acao = False
    parcial = bool(re.search(r'\b(faltando|aguardando|pendente|em andamento|em curadoria|'
                             r'enviad[oa]s? para (a )?curadoria|verificar depois)\b', texto))
    # Só contam números relacionados à inserção: "aguardando 20" não é prova.
    inseridos = [b for b in blocos if re.search(r'\binserid[oa]s?\b', b)
                 and not re.search(r'\bnao\s+(?:foi\s+)?inserid', b)]
    sessenta = any(re.search(r'\b60\b', b) for b in inseridos)
    vinte = any(re.search(r'\b20\b', b) for b in inseridos)
    return acao, parcial, sessenta, vinte


def resumir_threads(mensagens, agora=None):
    """Sugere status por thread, sem inferir conclusão de reação ou simples menção.

    Em ENADE exige evidência de 60 e 20 questões inseridas na mesma thread.
    Respostas de curadoria isoladas não substituem evidência de inserção.
    """
    agora = agora or datetime.now(timezone.utc)
    pais = {str(m['message_id']): m for m in mensagens
            if not m.get('parent_message_id') and not m.get('deleted_at')}
    respostas = defaultdict(list)
    for m in mensagens:
        if m.get('parent_message_id') and not m.get('deleted_at'):
            respostas[str(m['parent_message_id'])].append(m)
    saida = []
    for ident, pai in pais.items():
        equipe = sorted((m for m in respostas[ident] if m.get('author_user_id') in EQUIPE
                         and _normalizar(m.get('content'))
                         and not re.fullmatch(r'(?:natalia|lucas|pedro|stefanye|everson)'
                                              r'(?: (?:araujo|henrique|lima|marques|menezes|lustosa|da|de|do|broi|junior|ozorio))*',
                                              _normalizar(m.get('content')))),
                        key=lambda m: m['created_at'])
        titulo = pai.get('title') or ''
        enade = 'enade' in _normalizar(titulo + ' ' + (pai.get('content') or ''))
        conclusivas = []
        tem_60 = tem_20 = False
        pendencia_curadoria = False
        curadoria_feita = False
        outra_pendencia = False
        for m in equipe:
            acao, falta, sessenta, vinte = _marcadores(m.get('content'))
            texto = _normalizar(m.get('content'))
            insercao = bool(re.search(r'\b(inserid[oa]s?|insercao concluida)\b', texto))
            if insercao:
                tem_60 |= sessenta
                tem_20 |= vinte
            pendencia_curadoria |= falta and 'curadoria' in texto
            outra_pendencia |= falta and 'curadoria' not in texto and not (
                enade and ('20' in texto or '60' in texto))
            curadoria_feita |= bool(re.search(r'curadoria\s+(?:realizada|concluida|ok|feita)', texto))
            if acao:
                conclusivas.append(m)
        if not equipe:
            estado = 'sem resposta da equipe'
        elif enade and not (tem_60 and tem_20):
            estado = 'resposta parcial: faltam evidências de 60 e 20 questões inseridas'
        elif conclusivas and not (outra_pendencia or (pendencia_curadoria and not curadoria_feita)):
            estado = 'sugestão de conclusão'
        elif conclusivas and enade and tem_60 and tem_20:
            # Uma pendência de curadoria ainda importa; requer revisão humana.
            estado = 'inserção 60 e 20 confirmada; outra etapa pendente'
        elif conclusivas:
            estado = 'resposta parcial; conferir etapa pendente'
        else:
            estado = 'resposta sem confirmação de conclusão'
        inicio = datetime.fromisoformat(pai['created_at'].replace('Z', '+00:00'))
        saida.append({
            'message_id': ident, 'titulo': titulo, 'estado': estado,
            'created_at': pai['created_at'],
            'dias_desde_solicitacao': max(0, (agora.astimezone(FUSO).date() -
                                                  inicio.astimezone(FUSO).date()).days),
            'ultima_resposta_em': equipe[-1]['created_at'] if equipe else None,
            'evidencia': '\n'.join(f"{m.get('author_name')}: {m.get('content')}"
                                   for m in conclusivas)[:2000],
            'evidencias': [{'autor': m.get('author_name'), 'texto': m.get('content'),
                            'url': m.get('web_link')} for m in conclusivas],
            'url': pai.get('web_link'),
        })
    return sorted(saida, key=lambda x: x['dias_desde_solicitacao'], reverse=True)
