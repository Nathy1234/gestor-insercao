from flask import Flask, render_template, request, jsonify, redirect, url_for, session, flash, send_file, Response, abort
from flask_sqlalchemy import SQLAlchemy
from flask_wtf.csrf import CSRFProtect
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.exceptions import HTTPException
from itsdangerous import URLSafeTimedSerializer, BadSignature, SignatureExpired
from markupsafe import Markup, escape
from datetime import datetime, timedelta, date, timezone
from functools import wraps
import hashlib, os, secrets, shutil, json, threading, time, io, zipfile, unicodedata as _ucd, re as _re, calendar as _calendar
import requests as _requests
from urllib.parse import urlsplit, urlunsplit, parse_qs, urlencode
import icalendar as _icalendar
import recurring_ical_events as _recurring_ical_events

def _norm_name(s):
    """Remove acentos e converte para maiúsculo — para comparação de nomes de insersores."""
    return ''.join(c for c in _ucd.normalize('NFD', s.upper()) if _ucd.category(c) != 'Mn')

# Mapa de iniciais usadas no campo insersor (ex: 'P,L,S,F') para nome canônico normalizado
INICIAIS_INSERCAO = {
    'N': 'NATALIA', 'P': 'PEDRO', 'L': 'LUCAS',
    'S': 'STEFANYE', 'F': 'FELIPE', 'J': 'JUNIOR',
}

# Carrega variáveis do .env manualmente para não depender do python-dotenv
# e sem ativar DATABASE_URL (mantém SQLite local)
def _load_env_var(key):
    try:
        env_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), '.env')
        with open(env_path, encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line.startswith('#') or '=' not in line:
                    continue
                k, _, v = line.partition('=')
                if k.strip() == key:
                    return v.strip().strip('"').strip("'")
    except Exception:
        pass
    return None

# Carrega do .env (se não estiverem no ambiente) apenas as chaves de serviços
# externos — nunca SECRET_KEY/DATABASE_URL, pra manter SQLite local por padrão.
for _chave in ('ANTHROPIC_API_KEY', 'EMAIL_SMTP_USER', 'EMAIL_SMTP_PASSWORD'):
    if not os.environ.get(_chave):
        _val = _load_env_var(_chave)
        if _val and _val != 'sua-chave-aqui':
            os.environ[_chave] = _val

app = Flask(__name__)

# Versão exibida no rodapé — atualize aqui a cada mudança relevante publicada.
VERSAO = '1.19.51'
NO_AR_DESDE = '22/05/2026'

@app.context_processor
def inject_versao():
    return {'versao': VERSAO, 'no_ar_desde': NO_AR_DESDE}

@app.context_processor
def inject_ocultar_valores():
    """Disponível em todo template como `ocultar_valores` — True só pra
    conta de demonstração, pra mascarar R$ nas telas sem precisar checar
    role/permissão espalhado em cada arquivo."""
    ocultar = False
    if 'user_id' in session:
        u = User.query.get(session['user_id'])
        ocultar = bool(u and u.is_conta_demo())
    return {'ocultar_valores': ocultar}

_RE_NEGRITO = _re.compile(r'\*\*(.+?)\*\*')

def _aplica_negrito(texto_ja_escapado):
    """Troca **trecho** (já escapado) por <strong>trecho</strong>. Só mexe
    em texto que já passou por escape(), então é seguro — não introduz tag nova."""
    return _RE_NEGRITO.sub(r'<strong>\1</strong>', texto_ja_escapado)

@app.template_filter('texto_formatado')
def texto_formatado(texto):
    """Renderiza texto livre (descrição, observações) como HTML: linhas com
    TAB (coladas de uma planilha) viram uma tabela de verdade, **negrito**
    vira <strong>, o resto vira parágrafos. Todo conteúdo é escapado antes
    de qualquer substituição — texto pode vir de formulário público."""
    if not texto:
        return Markup('')
    linhas = texto.replace('\r\n', '\n').replace('\r', '\n').split('\n')
    blocos = []
    tabela_atual = []
    paragrafo_atual = []

    def fecha_paragrafo():
        if paragrafo_atual:
            html = '<br>'.join(_aplica_negrito(str(escape(l))) for l in paragrafo_atual)
            blocos.append('<p class="obs-paragrafo">' + html + '</p>')
            paragrafo_atual.clear()

    def fecha_tabela():
        if tabela_atual:
            linhas_html = []
            for linha in tabela_atual:
                celulas = ''.join('<td>' + _aplica_negrito(str(escape(c.strip()))) + '</td>' for c in linha.split('\t'))
                linhas_html.append('<tr>' + celulas + '</tr>')
            blocos.append('<table class="obs-tabela">' + ''.join(linhas_html) + '</table>')
            tabela_atual.clear()

    for linha in linhas:
        if '\t' in linha:
            fecha_paragrafo()
            tabela_atual.append(linha)
        elif linha.strip() == '':
            fecha_tabela()
            fecha_paragrafo()
        else:
            fecha_tabela()
            paragrafo_atual.append(linha)
    fecha_tabela()
    fecha_paragrafo()
    return Markup(''.join(blocos))

AREAS_VALIDAS = [
    'EDUCAÇÃO', 'SAÚDE', 'NEGÓCIOS', 'TECNOLOGIA',
    'CRIATIVIDADE', 'GASTRONOMIA', 'EVENTO',
]
TIPOS_CURSO = [
    'pos', 'profissionalizante', 'rapido', 'pacote', 'terceiros',
    'evento', 'pratica_conectada', 'pratica_estagio',
    'projeto_ambiental', 'ggbr', 'integra_edu',
]

# Matrizes Curriculares só faz sentido pra esses tipos — os demais (Rápido,
# Terceiros, Evento, Prática Conectada/Estágio, Proj. Ambiental, Integra Edu)
# não têm matriz nesse formato, então nem entram na tela.
MATRIZES_TIPOS_PERMITIDOS = {'pos', 'profissionalizante', 'pacote', 'ggbr'}

EQUIPE_INSERCAO = {'ADMIN', 'EVERSON', 'PEDRO', 'STEFANYE', 'LUCAS', 'FELIPE'}

def responsaveis_atuais():
    """Responsáveis por inserção de cursos = usuários cadastrados no sistema
    que fazem parte da equipe interna (admin, Everson, Pedro, Stéfanye, Lucas,
    Felipe). Contas de gente de fora da equipe não aparecem como responsável
    — pra adicionar/remover alguém da equipe, edite EQUIPE_INSERCAO."""
    return [u.username for u in User.query.order_by(User.username).all()
            if _norm_name(u.username) in EQUIPE_INSERCAO]

# Catálogo de widgets da dashboard — cada usuário escolhe quais mostrar e em
# que ordem (drag-and-drop), preferência salva em User.dashboard_prefs (JSON).
# Adicionar um widget novo aqui já faz ele aparecer (visível, no fim) pra quem
# já tinha personalizado a própria dashboard antes dele existir.
DASHBOARD_WIDGETS = [
    {'id': 'grafico',         'label': 'Gráfico — Cursos INOVA cadastrados'},
    {'id': 'ativos',          'label': 'Indicador — Ativos'},
    {'id': 'em_edicao',       'label': 'Indicador — Em edição'},
    {'id': 'finalizados',     'label': 'Card — Finalizados'},
    {'id': 'ocultos',         'label': 'Card — Ocultos'},
    {'id': 'descontinuados',  'label': 'Card — Descontinuados'},
    {'id': 'andamento',       'label': 'Andamento — Plataforma'},
    {'id': 'por_responsavel', 'label': 'Cursos por Responsável'},
    {'id': 'por_tipo',        'label': 'Distribuição por Tipo'},
    {'id': 'atividade',       'label': 'Atividade Recente'},
    {'id': 'atalhos',         'label': 'Acesso Rápido'},
    {'id': 'backup',          'label': 'Último Backup'},
    {'id': 'sem_responsavel', 'label': 'Cursos sem responsável'},
    {'id': 'reembolsos_pend', 'label': 'Reembolsos pendentes'},
    {'id': 'notas',           'label': 'Notas rápidas'},
    {'id': 'calendario_disciplinas', 'label': 'Calendário — Disciplinas por Módulo'},
]
_DASHBOARD_WIDGET_IDS = {w['id'] for w in DASHBOARD_WIDGETS}

# Versão do "significado" de row/col salvos em positions. Mudou de linha de
# grid única (auto-height) pra unidade fixa de 40px + rowspan por widget —
# uma posição salva no esquema antigo, se reaplicada literalmente no novo,
# empilha os widgets uns em cima dos outros. Positions salvas com versão
# diferente da atual são descartadas (o widget cai de volta pro
# auto-posicionamento em mosaico) em vez de reaplicadas erradas.
DASHBOARD_POSITIONS_VERSAO = 2

# Catálogo de módulos do menu lateral cujo acesso o admin controla — visível
# por padrão pra todo mundo, ou só pro admin, definido na tela Visibilidade
# (/admin/visibilidade). Cada conta ainda pode ser bloqueada individualmente
# por cima disso, na tela de editar usuário.
MODULOS_CATALOGO = [
    {'id': 'cursos',               'label': 'Cursos (catálogo, Pacotes, busca)'},
    {'id': 'matrizes',             'label': 'Matrizes Curriculares'},
    {'id': 'banco_disciplinas',    'label': 'Banco de Disciplinas'},
    {'id': 'ia_assistente',        'label': 'IA Assistente'},
    {'id': 'ferramentas',          'label': 'Ferramentas Externas'},
    {'id': 'historico',            'label': 'Histórico'},
    {'id': 'mural',                'label': 'Mural da Equipe'},
    {'id': 'formularios',          'label': 'Formulários'},
    {'id': 'calendario',           'label': 'Calendário'},
]
# Cupons, Reembolsos, Pagamentos Terceiros e Opções de Curso são financeiro/
# admin — moram fixos dentro de ADMIN no menu (User.can_manage_*), nem
# entram nesse padrão de visibilidade porque nunca aparecem em outro lugar.
MODULOS_PADRAO_VISIVEL = {
    'cursos': True, 'matrizes': True, 'banco_disciplinas': True,
    'ia_assistente': True, 'ferramentas': True, 'historico': True,
    'mural': True, 'formularios': True, 'calendario': True,
}

# Mesma lógica pros widgets da dashboard — "Último Backup" e "Reembolsos
# pendentes" são coisa de admin/financeiro, começam desligados pra quem não é.
DASHBOARD_WIDGETS_PADRAO_VISIVEL = {
    'grafico': True, 'ativos': True, 'em_edicao': True,
    'finalizados': True, 'ocultos': True, 'descontinuados': True,
    'andamento': True, 'por_responsavel': True, 'por_tipo': True,
    'atividade': True, 'atalhos': True, 'backup': False,
    'sem_responsavel': True, 'reembolsos_pend': False, 'notas': True,
    'calendario_disciplinas': True,
}

def _modulos_visiveis():
    """Padrão global (definido pelo admin em /admin/visibilidade) de quais
    módulos do menu ficam visíveis pra quem não é admin."""
    setting = AppSetting.query.get('modulos_visiveis')
    salvo = {}
    if setting and setting.value:
        try:
            salvo = json.loads(setting.value)
        except (ValueError, TypeError):
            salvo = {}
    return {k: salvo.get(k, v) for k, v in MODULOS_PADRAO_VISIVEL.items()}

def _modulo_visivel(key):
    return _modulos_visiveis().get(key, True)

def _widgets_dashboard_visiveis():
    """Padrão global de quais widgets da dashboard ficam disponíveis pra
    quem não é admin escolher em "Personalizar"."""
    setting = AppSetting.query.get('dashboard_widgets_visiveis')
    salvo = {}
    if setting and setting.value:
        try:
            salvo = json.loads(setting.value)
        except (ValueError, TypeError):
            salvo = {}
    return {k: salvo.get(k, v) for k, v in DASHBOARD_WIDGETS_PADRAO_VISIVEL.items()}

def get_dashboard_prefs(user):
    """Ordem, conjunto de ocultos, tamanhos (largura), alturas e posições
    (linha/coluna) livres da dashboard de `user`, já mesclado com o catálogo
    atual (widgets desconhecidos/removidos são descartados; widgets novos
    entram no fim, visíveis, no tamanho padrão e sem posição salva — o
    template calcula uma posição inicial pra eles). `tamanhos`/`alturas`/
    `posicoes` só têm entrada pros widgets que o usuário ajustou
    manualmente (arrastando a alça de redimensionar) — os demais usam a
    altura medida automaticamente a partir do conteúdo real."""
    try:
        prefs = json.loads(user.dashboard_prefs or '{}')
    except Exception:
        prefs = {}
    ordem_salva = [w for w in prefs.get('order', []) if w in _DASHBOARD_WIDGET_IDS]
    ocultos = {w for w in prefs.get('hidden', []) if w in _DASHBOARD_WIDGET_IDS}
    tamanhos_in = prefs.get('sizes', {}) if isinstance(prefs.get('sizes'), dict) else {}
    tamanhos = {}
    for wid, tam in tamanhos_in.items():
        if wid in _DASHBOARD_WIDGET_IDS and isinstance(tam, int) and 1 <= tam <= 4:
            tamanhos[wid] = tam
    alturas_in = prefs.get('heights', {}) if isinstance(prefs.get('heights'), dict) else {}
    alturas = {}
    for wid, alt in alturas_in.items():
        if wid in _DASHBOARD_WIDGET_IDS and isinstance(alt, int) and 1 <= alt <= 30:
            alturas[wid] = alt
    posicoes_in = (prefs.get('positions', {})
                   if isinstance(prefs.get('positions'), dict)
                   and prefs.get('positions_versao') == DASHBOARD_POSITIONS_VERSAO
                   else {})
    posicoes = {}
    for wid, pos in posicoes_in.items():
        if wid not in _DASHBOARD_WIDGET_IDS or not isinstance(pos, dict):
            continue
        r, c = pos.get('row'), pos.get('col')
        if isinstance(r, int) and isinstance(c, int) and 0 <= r <= 200 and 0 <= c <= 3:
            posicoes[wid] = {'row': r, 'col': c}
    faltando = [w['id'] for w in DASHBOARD_WIDGETS if w['id'] not in ordem_salva]
    return ordem_salva + faltando, ocultos, tamanhos, posicoes, alturas

def _insersor_contains(insersor_field, username):
    """Verifica se `username` está entre os insersores de um curso, aceitando
    tanto o nome completo quanto as iniciais legadas (ex: 'N' = Natália)."""
    if not insersor_field:
        return False
    un_norm = _norm_name(username)
    inicial = next((k for k, v in INICIAIS_INSERCAO.items() if v == un_norm), None)
    for parte in insersor_field.split(','):
        p = parte.strip()
        if _norm_name(p) == un_norm:
            return True
        if inicial and len(p) == 1 and p.upper() == inicial:
            return True
    return False

EMAIL_DOMINIO_PERMITIDO = '@fatecie.edu.br'
DIAS_INATIVIDADE = 7  # a partir de quantos dias sem logar alguém entra na lista de inativos
app.config['SECRET_KEY'] = os.environ.get('SECRET_KEY') or secrets.token_hex(32)
if not os.environ.get('SECRET_KEY'):
    print('[AVISO] SECRET_KEY não definida nas variáveis de ambiente. '
          'Gerando uma chave temporária para esta execução — os usuários serão '
          'desconectados a cada reinício do servidor. Defina SECRET_KEY no ambiente '
          '(Vercel/host) para sessões estáveis e seguras.')
app.config['PERMANENT_SESSION_LIFETIME'] = timedelta(days=7)
app.config['SESSION_PERMANENT'] = True
app.config['SESSION_COOKIE_HTTPONLY'] = True
app.config['SESSION_COOKIE_SAMESITE'] = 'Lax'
_db_url = os.environ.get('DATABASE_URL', 'sqlite:///inova.db')
if _db_url.startswith('postgres://'):
    _db_url = _db_url.replace('postgres://', 'postgresql://', 1)
# Em produção (Postgres) o cookie de sessão só trafega em HTTPS; em SQLite
# local (desenvolvimento) isso quebraria o login via http://localhost.
app.config['SESSION_COOKIE_SECURE'] = _db_url.startswith('postgresql://')
app.config['SQLALCHEMY_DATABASE_URI'] = _db_url
app.config['SQLALCHEMY_TRACK_MODIFICATIONS'] = False
if _db_url.startswith('postgresql://'):
    app.config['SQLALCHEMY_ENGINE_OPTIONS'] = {
        'connect_args': {
            'sslmode': 'require',
            'connect_timeout': 10,
        },
        'pool_pre_ping': True,
        'pool_size': 1,
        'max_overflow': 0,
        'pool_timeout': 20,
        'pool_recycle': 300,
    }
db = SQLAlchemy(app)
csrf = CSRFProtect(app)
limiter = Limiter(get_remote_address, app=app, storage_uri='memory://', default_limits=[])

# ─── E-MAIL ────────────────────────────────────────────────────────────────────
EMAIL_SMTP_USER = os.environ.get('EMAIL_SMTP_USER')
EMAIL_SMTP_PASSWORD = os.environ.get('EMAIL_SMTP_PASSWORD')


def enviar_email(destinatario, assunto, texto):
    """Envia e-mail via Gmail SMTP. Se EMAIL_SMTP_USER/PASSWORD não estiverem
    configurados, não falha — só registra no console, o que permite testar os
    fluxos de e-mail localmente sem precisar da conta configurada ainda."""
    if not destinatario:
        return False
    if not (EMAIL_SMTP_USER and EMAIL_SMTP_PASSWORD):
        print(f'[EMAIL SIMULADO — EMAIL_SMTP_USER/PASSWORD não configurados]\n'
              f'Para: {destinatario}\nAssunto: {assunto}\n\n{texto}\n')
        return True
    try:
        import smtplib
        from email.mime.text import MIMEText
        msg = MIMEText(texto, 'plain', 'utf-8')
        msg['Subject'] = assunto
        msg['From'] = f'Gestor Acadêmico <{EMAIL_SMTP_USER}>'
        msg['To'] = destinatario
        with smtplib.SMTP('smtp.gmail.com', 587, timeout=10) as server:
            server.starttls()
            server.login(EMAIL_SMTP_USER, EMAIL_SMTP_PASSWORD)
            server.sendmail(EMAIL_SMTP_USER, [destinatario], msg.as_string())
        return True
    except Exception as e:
        print(f'[ERRO EMAIL] {e}')
        return False

def enviar_email_com_anexo(destinatario, assunto, texto, anexo_bytes, anexo_nome):
    """Igual a enviar_email, mas com um arquivo anexado (usado pelos backups)."""
    if not destinatario:
        return False
    if not (EMAIL_SMTP_USER and EMAIL_SMTP_PASSWORD):
        print(f'[EMAIL SIMULADO — EMAIL_SMTP_USER/PASSWORD não configurados]\n'
              f'Para: {destinatario}\nAssunto: {assunto}\nAnexo: {anexo_nome} '
              f'({len(anexo_bytes)} bytes)\n\n{texto}\n')
        return True
    try:
        import smtplib
        from email.mime.multipart import MIMEMultipart
        from email.mime.text import MIMEText
        from email.mime.base import MIMEBase
        from email import encoders
        msg = MIMEMultipart()
        msg['Subject'] = assunto
        msg['From'] = f'Gestor Acadêmico <{EMAIL_SMTP_USER}>'
        msg['To'] = destinatario
        msg.attach(MIMEText(texto, 'plain', 'utf-8'))
        parte = MIMEBase('application', 'zip')
        parte.set_payload(anexo_bytes)
        encoders.encode_base64(parte)
        parte.add_header('Content-Disposition', f'attachment; filename="{anexo_nome}"')
        msg.attach(parte)
        with smtplib.SMTP('smtp.gmail.com', 587, timeout=20) as server:
            server.starttls()
            server.login(EMAIL_SMTP_USER, EMAIL_SMTP_PASSWORD)
            server.sendmail(EMAIL_SMTP_USER, [destinatario], msg.as_string())
        return True
    except Exception as e:
        print(f'[ERRO EMAIL] {e}')
        return False

def _telefone_whatsapp_normalizado(telefone):
    """Só dígitos, com DDI 55 na frente se a pessoa não tiver digitado
    (Z-API espera o telefone assim, ex: 5544999998888)."""
    digitos = _re.sub(r'\D', '', telefone or '')
    if digitos and not digitos.startswith('55'):
        digitos = '55' + digitos
    return digitos

def enviar_whatsapp(telefone, apikey, mensagem):
    """Envia via CallMeBot (gratuito) — cada pessoa ativa o próprio WhatsApp
    e gera sua apikey (ver instruções no Calendário → aba Alertas), não tem
    credencial compartilhada pro sistema todo. Sem telefone/apikey
    cadastrados, não falha — só registra no console, igual enviar_email faz
    com o SMTP."""
    telefone = _telefone_whatsapp_normalizado(telefone)
    if not telefone:
        return False
    if not apikey:
        try:
            print(f'[WHATSAPP SIMULADO - sem apikey do CallMeBot cadastrada]\nPara: {telefone}\n\n{mensagem}\n')
        except UnicodeEncodeError:
            pass  # console local (Windows/cp1252) pode não engolir emoji — nunca deve derrubar o envio por causa disso
        return True
    try:
        resp = _requests.get('https://api.callmebot.com/whatsapp.php',
                              params={'phone': telefone, 'text': mensagem, 'apikey': apikey}, timeout=15)
        if resp.status_code >= 400 or 'error' in resp.text.lower():
            print(f'[ERRO WHATSAPP] {resp.status_code} {resp.text[:300]}')
            return False
        return True
    except Exception as e:
        print(f'[ERRO WHATSAPP] {e}')
        return False

def _notificar_admins_whatsapp(categoria, mensagem):
    """Manda mensagem pra todo admin que tiver ligado essa categoria em
    Minha Conta (ver User.quer_whatsapp) — nunca deixa erro no envio
    (telefone inválido, Z-API fora do ar etc.) derrubar quem chamou."""
    try:
        for a in User.query.filter_by(role='admin').all():
            if a.quer_whatsapp(categoria):
                enviar_whatsapp(a.telefone_whatsapp, a.whatsapp_apikey, mensagem)
    except Exception as e:
        print(f'[ERRO NOTIFICAR ADMINS WHATSAPP] {e}')

def _notificar_disciplina_concluida(curso_nome, qtd, nome_disciplina=None):
    """Chamado em tempo real (não pelo cron) assim que uma disciplina é
    marcada como concluída no ERP Moodle (ver disciplina_toggle e
    disciplinas_marcar_todas)."""
    if qtd == 1 and nome_disciplina:
        texto = f'✅ Disciplina concluída — {curso_nome}: {nome_disciplina}'
    else:
        texto = f'✅ {qtd} disciplina(s) concluída(s) em {curso_nome}'
    _notificar_admins_whatsapp('disciplinas_concluidas', texto)

def _resumo_diario_sino():
    """Resumo do que hoje aparece no sino de notificações — disciplinas
    pendentes (não descontinuadas), eventos vencendo e solicitações
    recebidas via formulário. Roda 1x por dia (ver cron_backup), não em
    tempo real: os itens do sino mudam o dia inteiro em vários lugares
    diferentes do sistema pra valer a pena um aviso a cada mudança."""
    pendentes = Discipline.query.join(Course, Discipline.course_id == Course.id)\
        .filter(Discipline.plataforma_ok == False, Course.status.notin_(['descontinuado'])).count()
    eventos = len(_eventos_pendentes_ocultar())
    solicitacoes = Course.query.filter_by(via_formulario=True, status='em_edicao').count()
    finalizados = Course.query.filter_by(status='finalizado').count()
    if not (pendentes or eventos or solicitacoes or finalizados):
        return None
    return (f'📋 Resumo diário do Gestor Acadêmico:\n'
            f'- {pendentes} disciplina(s) pendente(s) no ERP Moodle\n'
            f'- {eventos} evento(s) com prazo vencendo\n'
            f'- {solicitacoes} solicitação(ões) recebida(s) aguardando\n'
            f'- {finalizados} curso(s) finalizado(s) aguardando publicação')

def _notificar_erro_plataforma(e):
    """Chamado pelo errorhandler global (ver erro_nao_tratado) assim que
    uma exceção não tratada estoura em qualquer rota."""
    rota = request.path if request else '?'
    texto = f'🚨 Erro no Gestor Acadêmico ({rota}): {type(e).__name__}: {str(e)[:200]}'
    _notificar_admins_whatsapp('erros_plataforma', texto)

def _reset_senha_serializer():
    return URLSafeTimedSerializer(app.config['SECRET_KEY'], salt='reset-senha')

# ─── MODELS ────────────────────────────────────────────────────────────────────

class User(db.Model):
    id           = db.Column(db.Integer, primary_key=True)
    username     = db.Column(db.String(80), unique=True, nullable=False)
    nome         = db.Column(db.String(200))  # nome completo, para exibição em e-mails
    email        = db.Column(db.String(200))
    password     = db.Column(db.String(200), nullable=False)
    must_change_password = db.Column(db.Boolean, default=False)
    role         = db.Column(db.String(20), default='viewer')  # admin, editor, viewer
    permissoes   = db.Column(db.Text, default='{}')  # JSON com permissoes especificas
    dashboard_prefs = db.Column(db.Text)  # JSON: {"order":[...], "hidden":[...]} dos widgets da dashboard
    notas_pessoais  = db.Column(db.Text)  # texto livre do widget "Notas rápidas" — só o próprio dono vê
    equipe       = db.Column(db.Boolean, default=True)  # faz parte da equipe?
    foto         = db.Column(db.LargeBinary)  # foto de perfil de exibição
    foto_mimetype = db.Column(db.String(50))
    telefone_whatsapp = db.Column(db.String(30))  # opcional — só usado se a pessoa optar por receber aviso no WhatsApp
    whatsapp_apikey = db.Column(db.String(50))  # apikey do CallMeBot (grátis) — gerada na ativação, ver instruções no Calendário → Alertas
    whatsapp_prefs = db.Column(db.Text)  # JSON: {"disciplinas_concluidas": true, "sino_diario": true, "erros_plataforma": true} — só admin configura
    agenda_ics_url = db.Column(db.Text)  # link secreto ICS da agenda pessoal (Outlook/Google) — reuniões de hoje/amanhã viram aviso
    agenda_ics_visibilidade = db.Column(db.String(20), default='pessoal')  # 'pessoal' (só eu vejo) ou 'todos' (aparece pra equipe inteira, marcado com meu nome)
    agenda_cache_json = db.Column(db.Text)  # cache das reuniões já buscadas no link acima, pra não bater na URL a cada carregamento de página
    agenda_cache_em = db.Column(db.DateTime)
    ultimo_login = db.Column(db.DateTime)  # usado pra listar colaboradores inativos e avisar quem voltou
    created_at   = db.Column(db.DateTime, default=datetime.utcnow)

    def get_perm(self, key):
        if self.role == 'admin':
            return True
        try:
            p = json.loads(self.permissoes or '{}')
        except:
            p = {}
        return p.get(key, False)

    def quer_whatsapp(self, categoria):
        """Só admin tem essas preferências (ver whatsapp_prefs) — precisa
        também ter telefone/apikey do CallMeBot cadastrados pra realmente
        receber algo."""
        if self.role != 'admin' or not self.telefone_whatsapp or not self.whatsapp_apikey:
            return False
        try:
            prefs = json.loads(self.whatsapp_prefs or '{}')
        except (ValueError, TypeError):
            prefs = {}
        return bool(prefs.get(categoria))

    def _p(self):
        try:
            return json.loads(self.permissoes or '{}')
        except:
            return {}

    def can_edit(self):
        return self.role in ('admin', 'editor') or self.get_perm('cursos_editar')

    def can_delete(self):
        return self.role == 'admin' or self.get_perm('cursos_excluir')

    def _modulo_ok(self, modulo_key, block_key):
        """Admin/editor interno sempre vê tudo. Pra viewer/editor comum: só
        aparece se o admin deixou o módulo visível por padrão (tela
        Visibilidade) E essa conta específica não foi bloqueada individualmente."""
        if self.role == 'admin':
            return True
        if not _modulo_visivel(modulo_key):
            return False
        return not self._p().get(block_key)

    def can_manage_cupons(self):
        """Cupons é módulo financeiro — fixo só pro admin, mora dentro de
        ADMIN no menu, não passa mais pelo padrão de visibilidade."""
        return self.role == 'admin'

    def can_view_cupons(self):
        """Só visualizar (sem criar/editar/excluir) — além do admin, só a
        conta de demonstração, pra ela conseguir mostrar o módulo inteiro."""
        return self.can_manage_cupons() or self.is_conta_demo()

    def can_manage_reembolsos(self):
        """Mesma coisa: Reembolsos é fixo só pro admin."""
        return self.role == 'admin'

    def can_view_reembolsos(self):
        return self.can_manage_reembolsos() or self.is_conta_demo()

    def can_view_historico(self):
        return self._modulo_ok('historico', 'block_historico')

    def can_manage_usuarios(self):
        return self.role == 'admin' or self.get_perm('usuarios_gerenciar')

    def can_manage_backup(self):
        return self.role == 'admin' or self.get_perm('backup_gerenciar')

    def can_view_cursos(self):
        return self._modulo_ok('cursos', 'block_cursos')

    def can_view_matrizes(self):
        return self._modulo_ok('matrizes', 'block_matrizes')

    def can_view_banco_disciplinas(self):
        return self._modulo_ok('banco_disciplinas', 'block_banco_disciplinas')

    def can_view_ia_assistente(self):
        return self._modulo_ok('ia_assistente', 'block_ia_assistente')

    def can_view_ferramentas(self):
        return self._modulo_ok('ferramentas', 'block_ferramentas')

    def can_view_mural(self):
        return self._modulo_ok('mural', 'block_mural')

    def can_view_formularios(self):
        return self._modulo_ok('formularios', 'block_formularios')

    def can_view_calendario(self):
        return self._modulo_ok('calendario', 'block_calendario')

    def can_manage_pagamentos_terceiros(self):
        """Fixo só pro admin — mora dentro de ADMIN no menu."""
        return self.role == 'admin'

    def can_view_pagamentos_terceiros(self):
        return self.can_manage_pagamentos_terceiros() or self.is_conta_demo()

    def can_manage_opcoes_curso(self):
        """Fixo só pro admin — mora dentro de ADMIN no menu."""
        return self.role == 'admin'

    def can_change_own_password(self):
        if self.role == 'admin': return True
        return not self._p().get('block_trocar_senha')

    def is_conta_demo(self):
        """Conta de vitrine: navega e vê tudo que o papel dela já libera, mas
        não consegue agir em nada (bloqueado globalmente em ensure_db/
        before_request), não vê valores em R$ (ver contexto 'ocultar_valores')
        e não emite relatório/exportação. Pensada pra link público de
        demonstração com dado fictício, sem risco de mexer ou vazar valor."""
        return self.role != 'admin' and bool(self._p().get('conta_demo'))

    def can_view_erp_moodle(self):
        """Enxerga a tela do ERP Moodle (inserção de conteúdo). Equipe interna
        (admin/editor) sempre vê; leitores só com a permissão explícita —
        usado para dar acesso à equipe externa de inserção."""
        if self.role in ('admin', 'editor'):
            return True
        return self.get_perm('erp_moodle_acesso')

    def can_edit_erp_moodle(self):
        """Só a equipe interna cria/edita itens — a equipe externa (viewer)
        só visualiza o andamento."""
        return self.role in ('admin', 'editor')

    def is_restrito_erp_moodle(self):
        """Conta usada só pela equipe externa: não deve ver nada além do
        ERP Moodle (nem cursos, financeiro, matrizes etc). Só faz efeito se
        a pessoa também tiver acesso ao ERP Moodle, pra nunca travar alguém
        do lado de fora sem enxergar nada."""
        if self.role == 'admin':
            return False
        return bool(self._p().get('somente_erp_moodle')) and self.can_view_erp_moodle()

class Course(db.Model):
    id            = db.Column(db.Integer, primary_key=True)
    nome          = db.Column(db.String(300), nullable=False)
    tipo          = db.Column(db.String(50))   # pos, profissionalizante, rapido, pacote, terceiros, evento, pratica, projeto
    area          = db.Column(db.String(100))
    horas         = db.Column(db.String(20))
    meses         = db.Column(db.String(20))
    valor         = db.Column(db.String(50))
    link_venda    = db.Column(db.Text)
    descricao     = db.Column(db.Text)
    link_imagem   = db.Column(db.Text)
    insersor      = db.Column(db.Text)  # pode ser comma-separated para múltiplos insersores
    obs           = db.Column(db.Text)
    status        = db.Column(db.String(30), default='ativo')  # ativo, descontinuado, em_edicao, oculto
    cupom         = db.Column(db.String(100))
    dono          = db.Column(db.Text)        # para cursos terceiros
    ano           = db.Column(db.String(10))  # ano de criação/edição do curso
    extra_data    = db.Column(db.Text)        # JSON com dados extras (matriz, disciplinas, etc.)
    venda_modalidade = db.Column(db.String(100))  # rótulo livre (Link, Site, ...) — vale p/ qualquer tipo de curso
    data_finalizacao = db.Column(db.Date)         # data de término — só relevante p/ tipo=evento
    link_video       = db.Column(db.Text)         # vídeo exibido na página de venda
    limite_parcelas  = db.Column(db.String(10))   # limite de parcelas — sobretudo cursos de pós
    via_formulario   = db.Column(db.Boolean, default=False)  # veio do formulário público de solicitação
    categoria     = db.Column(db.String(30), default='INOVA')  # INOVA — reservado p/ futuras linhas de produto
    created_at    = db.Column(db.DateTime, default=datetime.utcnow)
    updated_at    = db.Column(db.DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    created_by    = db.Column(db.Integer, db.ForeignKey('user.id'))

    @property
    def status_label(self):
        """Rótulo exibido nos badges — para eventos ativos, mostra 'Em
        Andamento' em vez de 'Ativo' (mesmo status internamente)."""
        if self.tipo == 'evento' and self.status == 'ativo':
            return 'Em Andamento'
        return (self.status or '').replace('_', ' ').title()

class Discipline(db.Model):
    id        = db.Column(db.Integer, primary_key=True)
    course_id = db.Column(db.Integer, db.ForeignKey('course.id'), nullable=False)
    modulo    = db.Column(db.String(100))
    ordem     = db.Column(db.Integer)
    nome      = db.Column(db.String(300), nullable=False)
    carga     = db.Column(db.String(20))
    professor = db.Column(db.String(200))
    cod_moodle    = db.Column(db.String(50))
    titulacao     = db.Column(db.String(50))
    plataforma_ok = db.Column(db.Boolean, default=False)
    plataforma_em = db.Column(db.DateTime)

class ErpMoodleItem(db.Model):
    """Acompanhamento de inserção de conteúdo no Moodle pela equipe de
    inserção de materiais — categoria própria (ERP MOODLE), separada do
    catálogo INOVA. Cadastro manual e independente de Course/Discipline:
    o curso pode ainda nem existir formalmente no catálogo."""
    id                   = db.Column(db.Integer, primary_key=True)
    nome_disciplina      = db.Column(db.String(300), nullable=False)
    nome_curso           = db.Column(db.String(300))  # digitado manualmente, sem vínculo com Course
    status               = db.Column(db.String(20), default='em_insercao')  # em_insercao, concluida
    data_conclusao       = db.Column(db.Date)
    insersor_responsavel = db.Column(db.String(200))
    observacao           = db.Column(db.Text)
    created_at           = db.Column(db.DateTime, default=datetime.utcnow)
    updated_at           = db.Column(db.DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    created_by           = db.Column(db.Integer, db.ForeignKey('user.id'))

    @property
    def status_label(self):
        return 'Concluída' if self.status == 'concluida' else 'Em Inserção'

class AuditLog(db.Model):
    id         = db.Column(db.Integer, primary_key=True)
    user_id    = db.Column(db.Integer, db.ForeignKey('user.id'))
    username   = db.Column(db.String(80))
    action     = db.Column(db.String(50))   # criar, editar, excluir, login
    entity     = db.Column(db.String(50))   # course, user, cupom
    entity_id  = db.Column(db.Integer)
    detail     = db.Column(db.Text)         # JSON do que mudou
    timestamp  = db.Column(db.DateTime, default=datetime.utcnow)

class Coupon(db.Model):
    id           = db.Column(db.Integer, primary_key=True)
    nome         = db.Column(db.String(100), nullable=False)
    quantidade   = db.Column(db.Integer)
    desconto     = db.Column(db.Float)
    cursos_tipo  = db.Column(db.String(100))
    limite_curso = db.Column(db.Integer)
    uso_unico    = db.Column(db.Boolean, default=True)
    data_inicial = db.Column(db.Date)
    data_final   = db.Column(db.Date)
    obs          = db.Column(db.Text)
    created_at   = db.Column(db.DateTime, default=datetime.utcnow)

class Refund(db.Model):
    id               = db.Column(db.Integer, primary_key=True)
    colab            = db.Column(db.String(100))
    nome_aluno       = db.Column(db.String(200))
    data_compra      = db.Column(db.Date)
    data_solicitacao = db.Column(db.Date)   # Solicitação do aluno
    valor            = db.Column(db.Float)
    valor_estorno    = db.Column(db.Float)
    nome_curso       = db.Column(db.String(300))
    categoria        = db.Column(db.String(100))
    solicitacao_1    = db.Column(db.Date)   # 1ª Solicitação (Nathy)
    solicitacao_2    = db.Column(db.Date)   # 2ª Solicitação (Jorge)
    data_aprovacao   = db.Column(db.Date)
    motivo           = db.Column(db.Text)
    curso_excluido   = db.Column(db.Date)   # Data exclusão do curso
    obs              = db.Column(db.Text)
    concluido_manual = db.Column(db.Boolean, default=False)
    created_at       = db.Column(db.DateTime, default=datetime.utcnow)
    # Dados para pagamento do reembolso
    cpf              = db.Column(db.String(20))
    celular          = db.Column(db.String(30))
    pix              = db.Column(db.String(200))
    email_destino    = db.Column(db.String(200))

    @property
    def pendencia(self):
        if self.concluido_manual:
            return ('concluido', 'Concluído')
        if not self.solicitacao_1:
            return ('sem_solic1', 'Aguarda 1ª Solicitação')
        if not self.solicitacao_2:
            return ('sem_solic2', 'Aguarda 2ª Solicitação')
        if not self.data_aprovacao:
            return ('sem_aprovacao', 'Aguarda Aprovação')
        if not self.curso_excluido:
            return ('sem_exclusao', 'Aguarda Exclusão do Curso')
        return ('concluido', 'Concluído')

class ThirdPartyPayment(db.Model):
    """Controle de repasses de venda para terceiros — restrito ao admin.
    Substitui a planilha manual usada antes para acompanhar o que já foi
    reportado/pago a cada parceiro."""
    id                = db.Column(db.Integer, primary_key=True)
    course_id         = db.Column(db.Integer, db.ForeignKey('course.id'), nullable=False)
    terceiro          = db.Column(db.String(150), nullable=False)
    data_emissao      = db.Column(db.Date)   # emissão/envio do relatório
    intervalo_inicio  = db.Column(db.Date)   # início do período de vendas reportado
    intervalo_fim     = db.Column(db.Date)   # fim do período de vendas reportado
    ano               = db.Column(db.String(10))
    valor             = db.Column(db.Float)
    obs               = db.Column(db.Text)
    created_at        = db.Column(db.DateTime, default=datetime.utcnow)
    created_by        = db.Column(db.Integer, db.ForeignKey('user.id'))

    curso = db.relationship('Course')

class BackupRecord(db.Model):
    id         = db.Column(db.Integer, primary_key=True)
    filename   = db.Column(db.String(200))
    size_kb    = db.Column(db.Float)
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    tipo       = db.Column(db.String(20), default='auto')  # auto, manual
    conteudo   = db.Column(db.LargeBinary)  # o .zip do backup, guardado no próprio banco

class VideoPreset(db.Model):
    """Links de vídeo usados com frequência na página de venda dos cursos
    (institucional, dos profissionalizantes/rápidos, da pós etc.) — editável
    pelo admin em vez de fixo no código, pra poder trocar quando precisar."""
    id     = db.Column(db.Integer, primary_key=True)
    label  = db.Column(db.String(200), nullable=False)
    url    = db.Column(db.Text, nullable=False)
    ordem  = db.Column(db.Integer, default=0)

class VendaModalidadeOpcao(db.Model):
    """Opções de 'Venda por' (Link, Site, ...) — editável pelo admin, não
    fica fixo em Link/Site; vale pra curso de qualquer tipo, não só eventos."""
    id     = db.Column(db.Integer, primary_key=True)
    label  = db.Column(db.String(100), nullable=False)
    ordem  = db.Column(db.Integer, default=0)

class ExternalTool(db.Model):
    """Sistemas externos (ex: Kronos) cadastrados pelo admin pra abrir
    embutidos dentro do próprio Gestor, sem precisar sair pra outra aba."""
    id         = db.Column(db.Integer, primary_key=True)
    label      = db.Column(db.String(150), nullable=False)
    url        = db.Column(db.Text, nullable=False)
    ordem      = db.Column(db.Integer, default=0)
    embeddable        = db.Column(db.Boolean)  # None = ainda não verificado
    embeddable_checado_em = db.Column(db.DateTime)
    created_at = db.Column(db.DateTime, default=datetime.utcnow)

class AppSetting(db.Model):
    """Configurações globais simples do sistema, tipo chave/valor — ex: a
    ordem das seções do menu lateral, escolhida pelo admin e valendo pra
    todo mundo (diferente do dashboard, que cada usuário organiza o seu)."""
    key   = db.Column(db.String(50), primary_key=True)
    value = db.Column(db.Text)

class MuralMensagem(db.Model):
    """Mural compartilhado da equipe — mensagem curta + reações em emoji e
    resposta a outra mensagem (thread simples), tudo público; ou, quando
    mencionado_id/privada estão preenchidos, uma mensagem de conversa 1-a-1
    que só autor e mencionado enxergam. Atualiza sozinho pra quem está com a
    tela aberta (poll) e avisa por e-mail quem recebeu mensagem privada e
    não está no sistema."""
    id            = db.Column(db.Integer, primary_key=True)
    user_id       = db.Column(db.Integer, db.ForeignKey('user.id'), nullable=False)
    texto         = db.Column(db.Text, nullable=False)
    resposta_a_id = db.Column(db.Integer, db.ForeignKey('mural_mensagem.id'))
    mencionado_id = db.Column(db.Integer, db.ForeignKey('user.id'))  # com quem é a conversa privada
    privada       = db.Column(db.Boolean, default=False)
    editado_em    = db.Column(db.DateTime)
    created_at    = db.Column(db.DateTime, default=datetime.utcnow)

    autor = db.relationship('User', foreign_keys=[user_id])
    mencionado = db.relationship('User', foreign_keys=[mencionado_id])
    resposta_a = db.relationship('MuralMensagem', remote_side=[id])

class MuralReacao(db.Model):
    """Uma reação em emoji de um usuário numa mensagem do mural. Uma pessoa
    pode reagir com vários emojis diferentes na mesma mensagem, mas não
    repetir o mesmo emoji duas vezes (clicar de novo remove)."""
    id           = db.Column(db.Integer, primary_key=True)
    mensagem_id  = db.Column(db.Integer, db.ForeignKey('mural_mensagem.id'), nullable=False)
    user_id      = db.Column(db.Integer, db.ForeignKey('user.id'), nullable=False)
    emoji        = db.Column(db.String(10), nullable=False)
    created_at   = db.Column(db.DateTime, default=datetime.utcnow)

    __table_args__ = (db.UniqueConstraint('mensagem_id', 'user_id', 'emoji', name='uq_reacao'),)

TIPOS_PERGUNTA_FORMULARIO = ('texto', 'numero', 'escala', 'multipla_escolha', 'sim_nao')

class Formulario(db.Model):
    """Formulário interno pra levantar indicadores da equipe — cada colaborador
    logado responde por si. Editar a estrutura depois nunca pode corromper o
    que já foi respondido (ver _salvar_perguntas_formulario)."""
    id             = db.Column(db.Integer, primary_key=True)
    titulo         = db.Column(db.String(200), nullable=False)
    descricao      = db.Column(db.Text)
    ativo          = db.Column(db.Boolean, default=True)    # aparece pra responder
    unica_resposta = db.Column(db.Boolean, default=True)    # True: reenviar atualiza a resposta da pessoa; False: cada envio vira um registro novo (pesquisa periódica)
    created_by     = db.Column(db.Integer, db.ForeignKey('user.id'))
    created_at     = db.Column(db.DateTime, default=datetime.utcnow)
    updated_at     = db.Column(db.DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)

class FormularioPergunta(db.Model):
    id            = db.Column(db.Integer, primary_key=True)
    formulario_id = db.Column(db.Integer, db.ForeignKey('formulario.id'), nullable=False)
    texto         = db.Column(db.Text, nullable=False)
    tipo          = db.Column(db.String(20), nullable=False)   # texto, numero, escala, multipla_escolha, sim_nao
    opcoes        = db.Column(db.Text)     # JSON list de strings — só multipla_escolha
    obrigatoria   = db.Column(db.Boolean, default=True)
    ordem         = db.Column(db.Integer, default=0)
    ativa         = db.Column(db.Boolean, default=True)    # False = removida do form, mas mantida pro histórico/indicadores
    created_at    = db.Column(db.DateTime, default=datetime.utcnow)

    def lista_opcoes(self):
        try:
            return json.loads(self.opcoes or '[]')
        except (ValueError, TypeError):
            return []

class FormularioResposta(db.Model):
    id            = db.Column(db.Integer, primary_key=True)
    formulario_id = db.Column(db.Integer, db.ForeignKey('formulario.id'), nullable=False)
    user_id       = db.Column(db.Integer, db.ForeignKey('user.id'), nullable=False)
    enviado_em    = db.Column(db.DateTime, default=datetime.utcnow)
    atualizado_em = db.Column(db.DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)

    colaborador = db.relationship('User', foreign_keys=[user_id])

class FormularioRespostaItem(db.Model):
    """Guarda um retrato da pergunta (texto/tipo) no momento em que foi
    respondida — assim, editar a pergunta depois nunca muda o que já foi
    registrado nem os indicadores já calculados a partir disso."""
    id             = db.Column(db.Integer, primary_key=True)
    resposta_id    = db.Column(db.Integer, db.ForeignKey('formulario_resposta.id'), nullable=False)
    pergunta_id    = db.Column(db.Integer, db.ForeignKey('formulario_pergunta.id'), nullable=False)
    pergunta_texto = db.Column(db.Text)
    pergunta_tipo  = db.Column(db.String(20))
    valor_texto    = db.Column(db.Text)     # texto livre, opção escolhida ou 'Sim'/'Não'
    valor_numero   = db.Column(db.Float)    # número ou escala

    resposta = db.relationship('FormularioResposta', backref='itens', foreign_keys=[resposta_id])
    pergunta = db.relationship('FormularioPergunta', foreign_keys=[pergunta_id])

STATUS_DEMANDA = ('stand_by', 'andamento', 'finalizado')
STATUS_DEMANDA_LABEL = {'stand_by': 'Em Stand By', 'andamento': 'Em Andamento', 'finalizado': 'Finalizado'}
MESES_PT = ['', 'Janeiro', 'Fevereiro', 'Março', 'Abril', 'Maio', 'Junho', 'Julho',
            'Agosto', 'Setembro', 'Outubro', 'Novembro', 'Dezembro']

def _usuarios_equipe_insercao():
    """Usuários que podem aparecer como responsável de uma demanda do
    Calendário (multi-seleção: uma demanda pode ter mais de um insersor).
    É todo mundo marcado como "Faz parte da equipe" (User.equipe) na tela
    de usuários — pra adicionar/remover alguém dessa lista, marque ou
    desmarque o checkbox lá, não precisa mexer em código."""
    usuarios = User.query.filter_by(equipe=True).all()
    return sorted(usuarios, key=lambda u: nome_exibicao(u))

class Demanda(db.Model):
    """Item do Calendário da equipe — uma demanda/tarefa com prazo, visível
    pra todo mundo. Só admin ajusta prazo/título/responsável ('configuração');
    qualquer um dos responsáveis designados também pode registrar a mudança
    de andamento (stand by / em andamento / finalizado) sem poder mexer no
    prazo. Pode ter mais de um responsável (vários insersores na mesma
    demanda) — guardado como ids separados por vírgula, tipo o campo
    `insersor` de Course."""
    id             = db.Column(db.Integer, primary_key=True)
    titulo         = db.Column(db.String(200), nullable=False)
    descricao      = db.Column(db.Text)
    data_inicio    = db.Column(db.Date, nullable=False)
    data_fim       = db.Column(db.Date, nullable=False)
    status         = db.Column(db.String(20), default='andamento')
    responsaveis   = db.Column(db.Text)  # ids de User separados por vírgula, ex: "3,7"
    created_by     = db.Column(db.Integer, db.ForeignKey('user.id'), nullable=False)
    created_at     = db.Column(db.DateTime, default=datetime.utcnow)
    updated_at     = db.Column(db.DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)

    # Aviso manual pra equipe toda ("avisar equipe") — disparado por um dos
    # responsáveis ou admin (mesma regra de pode_registrar_status). Fica
    # visível pra todo mundo até cada um clicar pra dispensar (ver
    # DemandaAlertaDispensa); disparar de novo limpa as dispensas antigas.
    alerta_texto      = db.Column(db.Text)
    alerta_ativo      = db.Column(db.Boolean, default=False)
    alerta_criado_em  = db.Column(db.DateTime)
    alerta_criado_por = db.Column(db.Integer, db.ForeignKey('user.id'))
    # Opcional, escolhido em cada disparo: manda WhatsApp (ver enviar_whatsapp)
    # pros responsáveis que tiverem telefone cadastrado — enviado uma vez só
    # por disparo, pelo cron diário (alerta_whatsapp_enviado zera a cada novo aviso).
    alerta_whatsapp          = db.Column(db.Boolean, default=False)
    alerta_whatsapp_enviado  = db.Column(db.Boolean, default=False)

    autor = db.relationship('User', foreign_keys=[created_by])

    def responsaveis_ids(self):
        return [int(x) for x in (self.responsaveis or '').split(',') if x.strip().isdigit()]

    def responsaveis_usuarios(self):
        ids = self.responsaveis_ids()
        if not ids:
            return []
        usuarios = User.query.filter(User.id.in_(ids)).all()
        ordem = {uid: i for i, uid in enumerate(ids)}
        return sorted(usuarios, key=lambda u: ordem.get(u.id, 999))

    def pode_editar(self, u):
        """Prazo, título, descrição e responsável — só admin."""
        return u.role == 'admin'

    def pode_registrar_status(self, u):
        """Marcar stand by / em andamento / finalizado — admin ou qualquer
        um dos responsáveis designados, sem precisar poder editar o prazo.
        Mesma regra usada pra disparar/cancelar o aviso da demanda."""
        return u.role == 'admin' or u.id in self.responsaveis_ids()

class DemandaAlertaDispensa(db.Model):
    """Quem já dispensou (clicou pra sumir) o aviso ativo de uma Demanda —
    por pessoa: sumir pra um não some pros outros. Disparar um aviso novo
    na mesma Demanda apaga essas dispensas, pra todo mundo ver de novo."""
    id         = db.Column(db.Integer, primary_key=True)
    demanda_id = db.Column(db.Integer, db.ForeignKey('demanda.id'), nullable=False)
    user_id    = db.Column(db.Integer, db.ForeignKey('user.id'), nullable=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow)

    __table_args__ = (db.UniqueConstraint('demanda_id', 'user_id', name='uq_demanda_alerta_dispensa'),)

class LembreteFixo(db.Model):
    """Lembrete mensal fixo e pessoal (ex: "todo dia 5 eu faço X") — cada
    usuário cadastra os seus, e só ele enxerga (nem admin vê o dos outros).
    Vira um aviso vermelho fixo no topo do sistema, em todas as telas, a
    partir de 1 dia antes do vencimento — e continua aparecendo (inclusive
    atrasado, contando os dias) até a própria pessoa clicar em "Já fiz
    isso"; não some sozinho com o tempo (ver _lembrete_pendencia)."""
    id                       = db.Column(db.Integer, primary_key=True)
    user_id                  = db.Column(db.Integer, db.ForeignKey('user.id'), nullable=False)
    titulo                   = db.Column(db.String(200), nullable=False)
    dia_mes                  = db.Column(db.Integer, nullable=False)  # 1–31; em mês mais curto, cai no último dia
    ativo                    = db.Column(db.Boolean, default=True)
    ultimo_checkin_ocorrencia = db.Column(db.Date)  # última ocorrência que a pessoa já confirmou ter feito
    # Opcional: além do aviso no sistema, manda WhatsApp (ver enviar_whatsapp)
    # pro telefone cadastrado da própria pessoa, uma vez por ocorrência pendente.
    avisar_whatsapp          = db.Column(db.Boolean, default=False)
    ultimo_whatsapp_ocorrencia = db.Column(db.Date)
    created_at               = db.Column(db.DateTime, default=datetime.utcnow)

def _lembrete_pendencia(lembrete, hoje=None):
    """Calcula se um LembreteFixo está pendente hoje. A partir de 1 dia
    antes do dia fixo do mês ele entra "em janela" e continua pendente -
    inclusive atrasado, contando os dias corridos - até a pessoa confirmar
    (ultimo_checkin_ocorrencia); nunca some sozinho só por o tempo passar.
    Ajusta o dia fixo pro último dia do mês quando ele for mais curto (ex:
    dia_mes=31 cai em 28/29 em fevereiro). Retorna None quando não há nada
    pendente ainda, ou um dict {ocorrencia, status, dias_atraso}."""
    hoje = hoje or date.today()
    dia_mes = lembrete.dia_mes

    def _ocorrencia(delta_mes):
        mes, ano = hoje.month + delta_mes, hoje.year
        while mes < 1:
            mes += 12; ano -= 1
        while mes > 12:
            mes -= 12; ano += 1
        ultimo_dia = _calendar.monthrange(ano, mes)[1]
        return date(ano, mes, min(dia_mes, ultimo_dia))

    candidatas = sorted({_ocorrencia(-1), _ocorrencia(0), _ocorrencia(1)})
    pendente = None
    for oc in candidatas:
        if hoje >= oc - timedelta(days=1):
            pendente = oc  # fica com a mais recente cuja janela já abriu
    if pendente is None:
        return None
    if lembrete.ultimo_checkin_ocorrencia and lembrete.ultimo_checkin_ocorrencia >= pendente:
        return None
    dias_atraso = (hoje - pendente).days
    status = 'amanha' if dias_atraso < 0 else ('hoje' if dias_atraso == 0 else 'atrasado')
    return {'ocorrencia': pendente, 'status': status, 'dias_atraso': dias_atraso}

def _lembrete_para_exibir(l, hoje=None):
    """Monta o dict usado tanto no aviso global (inject_notificacoes) quanto
    na lista de gerenciamento (aba Alertas) — uma função só, pra nunca os
    dois lugares calcularem a pendência de um jeito diferente."""
    pend = _lembrete_pendencia(l, hoje)
    if not pend:
        return {'id': l.id, 'titulo': l.titulo, 'dia_mes': l.dia_mes, 'status': None, 'dias_atraso': 0,
                'label': None, 'avisar_whatsapp': l.avisar_whatsapp}
    label = {'hoje': 'HOJE', 'amanha': 'AMANHÃ'}.get(pend['status'], f"ATRASADO {pend['dias_atraso']}D")
    return {'id': l.id, 'titulo': l.titulo, 'dia_mes': l.dia_mes,
            'status': pend['status'], 'dias_atraso': pend['dias_atraso'], 'label': label,
            'avisar_whatsapp': l.avisar_whatsapp}

_BRASIL_TZ = timezone(timedelta(hours=-3))

AGENDA_DIAS_JANELA = 7  # até quantos dias à frente uma reunião já aparece no aviso do topo

def _buscar_reunioes_ics(url, hoje):
    """Busca e interpreta o link ICS de verdade — deixa a exceção subir (o
    chamador decide o que fazer: cair pro cache, ou mostrar o erro exato
    pra pessoa, no botão "Testar agora")."""
    resp = _requests.get(url, timeout=8, headers={'User-Agent': 'Mozilla/5.0 (compatible; GestorAcademico/1.0)'})
    resp.raise_for_status()
    cal = _icalendar.Calendar.from_ical(resp.content)
    fim_janela = hoje + timedelta(days=AGENDA_DIAS_JANELA)
    ocorrencias = _recurring_ical_events.of(cal).between(hoje, fim_janela + timedelta(days=1))
    eventos = []
    for ev in ocorrencias:
        inicio = ev.get('dtstart').dt
        if isinstance(inicio, datetime):
            if inicio.tzinfo:
                inicio = inicio.astimezone(_BRASIL_TZ)
            dia = inicio.date()
            hora = inicio.strftime('%H:%M')
        else:
            dia = inicio
            hora = None
        dias_para = (dia - hoje).days
        if dias_para < 0 or dias_para > AGENDA_DIAS_JANELA:
            continue
        if dias_para == 0:
            label = 'HOJE'
        elif dias_para == 1:
            label = 'AMANHÃ'
        else:
            label = f'EM {dias_para} DIAS ({dia.strftime("%d/%m")})'
        eventos.append({
            'titulo': str(ev.get('summary') or 'Sem título'),
            'hora': hora, 'dias_para': dias_para, 'label': label,
        })
    eventos.sort(key=lambda e: (e['dias_para'], e['hora'] or ''))
    return eventos

def _reunioes_hoje_amanha(u, hoje=None):
    """Reuniões dos próximos AGENDA_DIAS_JANELA dias a partir do link ICS da
    agenda pessoal (Outlook/Google, ver campo agenda_ics_url) — cacheia o
    resultado por 20 minutos (agenda_cache_json/agenda_cache_em) pra não
    buscar a URL externa a cada carregamento de página. Nunca deixa a
    agenda fora do ar ou mal configurada quebrar a tela: qualquer erro cai
    no cache antigo (ou lista vazia, se nunca buscou) — pra ver o erro de
    verdade, usa o botão "Testar agora" (ver calendario_agenda_ics_testar)."""
    if not u.agenda_ics_url:
        return []
    hoje = hoje or date.today()
    cache_valido = u.agenda_cache_em and (datetime.utcnow() - u.agenda_cache_em) < timedelta(minutes=20)
    if not cache_valido:
        try:
            eventos = _buscar_reunioes_ics(u.agenda_ics_url, hoje)
            u.agenda_cache_json = json.dumps(eventos, ensure_ascii=False)
            u.agenda_cache_em = datetime.utcnow()
            db.session.commit()
            return eventos
        except Exception as e:
            print(f'[ERRO AGENDA ICS] usuario={u.id}: {e}')
            # cai pro cache antigo abaixo em vez de quebrar a tela
    try:
        return json.loads(u.agenda_cache_json or '[]')
    except (ValueError, TypeError):
        return []

STATUS_DISC_MODULO = ('nao_iniciado', 'em_producao', 'em_andamento', 'inserida', 'liberada_moodle', 'liberada_inova')
# 'em_curadoria' saiu das opções (não é mais escolhível), mas o label/cor
# continuam mapeados abaixo pra disciplina antiga que ainda tiver esse
# status salvo no banco não quebrar a tela.
STATUS_DISC_MODULO_LABEL = {
    'nao_iniciado':    'Selecionar…',
    'em_producao':     'Stand-by',
    'em_andamento':    'Em Andamento',
    'inserida':        'Inserida',
    'em_curadoria':    'Em Curadoria',
    'liberada_moodle': 'Liberada no Moodle',
    'liberada_inova':  'Liberada no Inova',
}
STATUS_DISC_MODULO_COR = {
    'nao_iniciado':    '#a1a1aa',
    'em_producao':     '#78716c',
    'em_andamento':    '#ca8a04',
    'inserida':        '#1d4ed8',
    'em_curadoria':    '#b35700',
    'liberada_moodle': '#15803d',
    'liberada_inova':  '#7c3aed',
}
# Ordem em que cada status aparece agrupado na listagem de disciplinas por
# Tipo/Módulo — liberadas primeiro (0), depois do mais avançado no processo
# pro menos avançado. Quem não está mapeado aqui cai no fim (ver .get(..., 99)).
_PRIORIDADE_STATUS_LISTAGEM = {
    'liberada_moodle': 0, 'liberada_inova': 0,
    'inserida': 1,
    'em_andamento': 2,
    'em_producao': 3,
    'em_curadoria': 4,
    'nao_iniciado': 5,
}

class ModuloCalendario(db.Model):
    """Lista de TIPOS disponíveis pra agrupar as disciplinas de inserção —
    gerenciada pelo admin, pra não digitar o nome do zero toda vez (ex:
    'APA CLARA IA', 'GRADUAÇÃO TEÓRICA'). O nome da coluna/tabela ficou
    'módulo' por histórico, mas na interface e no resto do código isso é
    chamado de Tipo — é o nível de cima, um degrau acima do Módulo
    (SubmoduloCalendario). Vínculo com DisciplinaModulo é pelo nome
    (texto), não por FK — renomear aqui atualiza em cascata as disciplinas
    que já usam o nome antigo."""
    id         = db.Column(db.Integer, primary_key=True)
    nome       = db.Column(db.String(200), nullable=False, unique=True)
    ordem      = db.Column(db.Integer, default=0)
    created_by = db.Column(db.Integer, db.ForeignKey('user.id'))
    created_at = db.Column(db.DateTime, default=datetime.utcnow)

class SubmoduloCalendario(db.Model):
    """MÓDULO — segundo nível, dentro de um Tipo (ex: 'Módulo 1', 'Módulo
    2', 'ANO/1'). A lista de nomes é global e cadastrada uma vez só —
    aparece disponível pra escolher dentro de QUALQUER Tipo — mas os
    nomes se repetindo entre Tipos não significa que a informação se
    repete: as disciplinas de "Módulo 1" em "APA CLARA IA" são
    completamente independentes das de "Módulo 1" em "GRADUAÇÃO TEÓRICA".
    Vínculo com DisciplinaModulo é pelo nome (texto), igual ModuloCalendario."""
    id         = db.Column(db.Integer, primary_key=True)
    nome       = db.Column(db.String(200), nullable=False, unique=True)
    ordem      = db.Column(db.Integer, default=0)
    created_by = db.Column(db.Integer, db.ForeignKey('user.id'))
    created_at = db.Column(db.DateTime, default=datetime.utcnow)

class DisciplinaModulo(db.Model):
    """Disciplina cadastrada dentro de um Tipo e, dentro dele, um Módulo —
    lista própria da equipe (separada do Banco de Disciplinas / ERP Moodle)
    pra acompanhar o andamento de cada uma, do início da produção até
    liberada no Moodle, e aparecer também na página pública do Calendário.
    Tipo e Módulo são livres (o admin cadastra o que fizer sentido). Só
    admin cria/edita/exclui a estrutura ('configuração'); qualquer um da
    equipe pode clicar pra registrar em que etapa ela está."""
    id           = db.Column(db.Integer, primary_key=True)
    modulo       = db.Column(db.String(200), nullable=False)  # Tipo (nome histórico da coluna)
    submodulo    = db.Column(db.String(200))                  # Módulo, dentro do Tipo — pode ficar vazio
    nome         = db.Column(db.String(300), nullable=False)
    carga        = db.Column(db.String(20))     # carga horária — preenchida ao colar da planilha (2ª coluna)
    professor    = db.Column(db.String(200))    # preenchido ao colar da planilha (3ª coluna)
    status       = db.Column(db.String(20), default='nao_iniciado')
    status_em    = db.Column(db.DateTime, default=datetime.utcnow)
    observacao   = db.Column(db.Text)
    ordem        = db.Column(db.Integer, default=0)
    arquivado    = db.Column(db.Boolean, default=False)  # tira da listagem ativa sem apagar dado
    created_by   = db.Column(db.Integer, db.ForeignKey('user.id'), nullable=False)
    created_at   = db.Column(db.DateTime, default=datetime.utcnow)
    updated_at   = db.Column(db.DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)

    autor = db.relationship('User', foreign_keys=[created_by])

# ─── HELPERS ───────────────────────────────────────────────────────────────────

def _parse_data_form(valor):
    """Converte string 'YYYY-MM-DD' de um <input type=date> em date. Vazio -> None."""
    valor = (valor or '').strip()
    if not valor:
        return None
    try:
        return datetime.strptime(valor, '%Y-%m-%d').date()
    except ValueError:
        return None

def _eventos_pendentes_ocultar():
    """Eventos 'em andamento' (status=ativo) cuja data de finalização já
    chegou ou é amanhã — precisam ser ocultados manualmente da plataforma."""
    limite = date.today() + timedelta(days=1)
    return Course.query.filter(
        Course.tipo == 'evento', Course.status == 'ativo',
        Course.data_finalizacao != None, Course.data_finalizacao <= limite
    ).order_by(Course.data_finalizacao).all()

@app.template_filter('nome_exibicao')
def nome_exibicao(u):
    """Nome de exibição de um usuário — trata também a string literal
    "None" que algum import antigo pode ter deixado no lugar de vazio."""
    if not u:
        return '—'
    nome = (u.nome or '').strip()
    if nome and nome.lower() != 'none':
        return nome
    return u.username

@app.template_global('agrupar_ferramentas')
def _agrupar_ferramentas(tools):
    """Agrupa ferramentas externas automaticamente por padrão do nome/URL,
    pra não empilhar tudo solto na barra lateral: rótulo começando com
    'Moodle' vira o grupo MOODLE, planilhas/links de disciplinas viram o
    grupo DISCIPLINAS — mas um link direto de pasta do Drive fica solto
    (não faz sentido um grupo de um item só). Zero configuração manual."""
    grupos_ordem = ['MOODLE', 'DISCIPLINAS']
    grupos = {nome: [] for nome in grupos_ordem}
    soltas = []
    for t in tools:
        label_low = (t.label or '').lower()
        url_low = (t.url or '').lower()
        if label_low.startswith('moodle'):
            grupos['MOODLE'].append(t)
        elif 'drive.google.com' in url_low:
            soltas.append(t)
        elif 'disc' in label_low:
            grupos['DISCIPLINAS'].append(t)
        else:
            soltas.append(t)
    grupos_finais = [(nome, grupos[nome]) for nome in grupos_ordem if grupos[nome]]
    return soltas, grupos_finais

def hash_pw(pw): return generate_password_hash(pw)

def check_pw(stored_hash, plain_pw):
    """Verifica a senha. Aceita hashes novos (werkzeug, com salt) e os
    hashes antigos em SHA-256 puro criados antes desta correção de segurança."""
    if stored_hash.startswith(('pbkdf2:', 'scrypt:')):
        return check_password_hash(stored_hash, plain_pw)
    return stored_hash == hashlib.sha256(plain_pw.encode()).hexdigest()

def login_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if 'user_id' not in session:
            return redirect(url_for('login'))
        if not User.query.get(session['user_id']):
            return _sessao_invalida()
        return f(*args, **kwargs)
    return decorated

def _sessao_invalida():
    session.clear()
    flash('Sua sessão expirou. Faça login novamente.', 'warning')
    return redirect(url_for('login'))

def admin_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if 'user_id' not in session:
            return redirect(url_for('login'))
        u = User.query.get(session['user_id'])
        if not u:
            return _sessao_invalida()
        if u.role != 'admin':
            flash('Acesso restrito a administradores.', 'danger')
            return redirect(url_for('dashboard'))
        return f(*args, **kwargs)
    return decorated

def editor_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if 'user_id' not in session:
            return redirect(url_for('login'))
        u = User.query.get(session['user_id'])
        if not u:
            return _sessao_invalida()
        if u.role not in ('admin', 'editor'):
            flash('Sem permissão para editar.', 'danger')
            return redirect(url_for('dashboard'))
        return f(*args, **kwargs)
    return decorated

def perm_check(check_fn_name):
    """Decorator que verifica uma permissão específica via método do User model."""
    def decorator(f):
        @wraps(f)
        def decorated(*args, **kwargs):
            if 'user_id' not in session:
                return redirect(url_for('login'))
            u = User.query.get(session['user_id'])
            if not u:
                return _sessao_invalida()
            if not getattr(u, check_fn_name)():
                flash('Você não tem permissão para acessar esta seção.', 'danger')
                return redirect(url_for('dashboard'))
            return f(*args, **kwargs)
        return decorated
    return decorator

def log_action(user_id, username, action, entity, entity_id, detail=''):
    entry = AuditLog(user_id=user_id, username=username, action=action,
                     entity=entity, entity_id=entity_id, detail=detail)
    db.session.add(entry)
    db.session.commit()

def _resumo_mudancas(antes, depois, labels):
    """Compara os valores de campos simples antes/depois de uma edição e monta
    um texto tipo 'Campo: "antigo" -> "novo"; ...' pra usar no histórico —
    em vez de só registrar que algo foi editado, mostra o que mudou."""
    partes = []
    for campo, label in labels.items():
        va = '' if antes.get(campo) is None else str(antes.get(campo))
        vn = '' if depois.get(campo) is None else str(depois.get(campo))
        if va.strip() == vn.strip():
            continue
        va_show = (va.strip() or '—')[:60]
        vn_show = (vn.strip() or '—')[:60]
        partes.append(f'{label}: "{va_show}" → "{vn_show}"')
    return '; '.join(partes)

BACKUP_MODELOS = [User, Course, Discipline, AuditLog, Coupon, Refund, ThirdPartyPayment, ErpMoodleItem,
                  Formulario, FormularioPergunta, FormularioResposta, FormularioRespostaItem]

def _serializar_valor(v):
    if isinstance(v, (datetime, date)):
        return v.isoformat()
    return v

def _dump_dados_json():
    """Exporta todas as tabelas de dados (menos os backups em si) para um
    dicionário serializável em JSON. Usa os modelos do SQLAlchemy em vez de
    copiar um arquivo — por isso funciona igual em SQLite e em Postgres."""
    dados = {}
    for modelo in BACKUP_MODELOS:
        linhas = []
        for obj in modelo.query.all():
            linha = {col.name: _serializar_valor(getattr(obj, col.name))
                      for col in modelo.__table__.columns}
            linhas.append(linha)
        dados[modelo.__tablename__] = linhas
    return dados

def make_backup(tipo='auto'):
    with app.app_context():
        dados = _dump_dados_json()
        json_bytes = json.dumps(dados, ensure_ascii=False, default=str).encode('utf-8')
        ts = datetime.now().strftime('%Y%m%d_%H%M%S')
        fname = f'backup_{tipo}_{ts}.zip'
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, 'w', zipfile.ZIP_DEFLATED) as zf:
            zf.writestr('dados.json', json_bytes)
        conteudo = buf.getvalue()
        size_kb = len(conteudo) / 1024

        rec = BackupRecord(filename=fname, size_kb=round(size_kb, 2), tipo=tipo, conteudo=conteudo)
        db.session.add(rec)
        db.session.commit()

        # Mantém só os últimos 20 backups guardados no banco
        bks = BackupRecord.query.order_by(BackupRecord.created_at.asc()).all()
        if len(bks) > 20:
            for old in bks[:-20]:
                db.session.delete(old)
            db.session.commit()

        # Envia uma cópia por e-mail — independente do banco de produção,
        # então continua existindo mesmo se o banco for perdido de vez.
        destino = os.environ.get('EMAIL_BACKUP_DESTINO', EMAIL_SMTP_USER)
        if destino:
            enviar_email_com_anexo(
                destino,
                f'Backup ({tipo}) — Gestor Acadêmico — {ts}',
                f'Backup gerado em {datetime.now().strftime("%d/%m/%Y %H:%M")}.\n'
                f'Tamanho: {round(size_kb, 1)} KB.\n\n'
                'O anexo contém todos os dados do sistema em formato JSON, dentro de um .zip.',
                conteudo, fname,
            )
        return rec

def backup_scheduler():
    """Só roda se o processo 'python app.py' ficar ligado continuamente
    (ambiente local). Em produção (Vercel), o agendamento é feito pelo
    Vercel Cron chamando a rota /cron/backup."""
    while True:
        time.sleep(24 * 3600)  # diário
        make_backup(tipo='auto')

def _desserializar_valor(valor, coluna):
    if valor is None:
        return None
    try:
        py_type = coluna.type.python_type
    except NotImplementedError:
        return valor
    if py_type is datetime:
        return datetime.fromisoformat(valor)
    if py_type is date:
        return date.fromisoformat(valor)
    return valor

# Ordem que respeita as chaves estrangeiras: Discipline depende de Course,
# Course e AuditLog dependem de User — então apaga nessa ordem e insere ao contrário.
RESTORE_ORDEM_APAGAR   = [ThirdPartyPayment, Discipline, Course, AuditLog, Coupon, Refund, ErpMoodleItem, User]
RESTORE_ORDEM_INSERIR  = [User, Course, Discipline, AuditLog, Coupon, Refund, ThirdPartyPayment, ErpMoodleItem]

def restaurar_backup(dados):
    """Substitui TODOS os dados atuais pelos do backup (mesmo formato gerado
    por _dump_dados_json). Roda dentro de uma única transação: se der erro no
    meio, nada fica pela metade — a chamadora decide se faz commit ou rollback."""
    for modelo in RESTORE_ORDEM_APAGAR:
        modelo.query.delete()
    db.session.flush()

    for modelo in RESTORE_ORDEM_INSERIR:
        linhas = dados.get(modelo.__tablename__, [])
        colunas = {c.name: c for c in modelo.__table__.columns}
        for linha in linhas:
            valores = {k: _desserializar_valor(v, colunas[k]) for k, v in linha.items() if k in colunas}
            db.session.add(modelo(**valores))
        db.session.flush()

    # Reajusta os contadores de auto-incremento do Postgres, senão o próximo
    # INSERT normal (sem ID explícito) pode colidir com um ID restaurado.
    if _db_url.startswith('postgresql://'):
        for modelo in RESTORE_ORDEM_INSERIR:
            db.session.execute(db.text(
                f"SELECT setval(pg_get_serial_sequence('{modelo.__tablename__}', 'id'), "
                f"COALESCE((SELECT MAX(id) FROM {modelo.__tablename__}), 1))"
            ))

@app.context_processor
def inject_now():
    return {'now': datetime.now}

def _sidebar_section_order():
    """Ordem das seções do menu lateral escolhida pelo admin (vale pra todo
    mundo). Lista vazia = ordem padrão (a ordem em que já estão no HTML)."""
    setting = AppSetting.query.get('sidebar_section_order')
    if not setting or not setting.value:
        return []
    try:
        return json.loads(setting.value)
    except (ValueError, TypeError):
        return []

def _modulos_ordem():
    """Ordem dos itens/subcategorias dentro de cada seção do menu (ex: a
    ordem de Cursos/Cupons/Reembolsos/... dentro de INOVA CARREIRA) —
    global, escolhida pelo admin, mesmo princípio da ordem das seções. Só
    define POSIÇÃO — quem enxerga cada item continua sendo decidido pelas
    permissões/visibilidade de cada um, isso aqui nunca libera nem esconde
    nada."""
    setting = AppSetting.query.get('modulos_ordem')
    if not setting or not setting.value:
        return []
    try:
        return json.loads(setting.value)
    except (ValueError, TypeError):
        return []

@app.context_processor
def inject_notificacoes():
    if 'user_id' not in session:
        return {}
    u = User.query.get(session['user_id'])
    if not u:
        return {}
    if u.is_restrito_erp_moodle():
        # Conta restrita à equipe externa — nem calcula notificações do
        # catálogo INOVA, que ela não tem acesso a ver.
        return {
            'notif_count': 0, 'notif_list': [], 'admin_finalizado': [], 'admin_finalizado_count': 0,
            'eventos_pendentes': [], 'eventos_pendentes_count': 0,
            'solicitacoes_pendentes': [], 'solicitacoes_pendentes_count': 0,
            'can_cupons': False, 'can_reembolsos': False, 'can_historico': False,
            'can_erp_moodle': True, 'somente_erp_moodle': True, 'ferramentas_tools': [],
            'sidebar_section_order': [], 'modulos_ordem': [],
            'can_cursos': False, 'can_matrizes': False, 'can_banco_disciplinas': False,
            'can_ia_assistente': False, 'can_ferramentas': False,
            'can_pagamentos_terceiros': False, 'can_opcoes_curso': False,
            'can_mural': False, 'can_formularios': False, 'can_calendario': False,
            'lembretes_ativos': [], 'alertas_demandas_ativos': [], 'reunioes_ativas': [],
        }
    # Disciplinas pendentes (plataforma_ok=False) em cursos atribuídos a este usuário
    q = db.session.query(Discipline, Course)\
        .join(Course, Discipline.course_id == Course.id)\
        .filter(Discipline.plataforma_ok == False)\
        .filter(Course.status.notin_(['descontinuado']))
    if u.role != 'admin':
        # Sem insersor não há responsável a notificar
        q = q.filter(Course.insersor != None, Course.insersor != '')
    rows = q.order_by(Course.nome, Discipline.ordem).all()
    if u.role != 'admin':
        # Filtra em Python (não em SQL) para reconhecer também as iniciais
        # legadas (ex: curso com insersor='N' deve notificar a Natália).
        rows = [(disc, curso) for disc, curso in rows if _insersor_contains(curso.insersor, u.username)]
    pendentes = rows

    by_course = {}
    for disc, curso in pendentes:
        if curso.id not in by_course:
            by_course[curso.id] = {'course': curso, 'discs': [], 'total': 0}
        by_course[curso.id]['discs'].append(disc)
        by_course[curso.id]['total'] += 1

    notif_list = sorted(by_course.values(), key=lambda x: x['total'], reverse=True)[:8]

    # Para admin: cursos marcados como finalizado aguardando publicação
    admin_finalizado = []
    if u.role == 'admin':
        admin_finalizado = Course.query.filter_by(status='finalizado')\
            .order_by(Course.updated_at.desc()).limit(15).all()

    # Eventos com data de finalização vencendo — só quem pode editar cursos vê
    eventos_pendentes = []
    solicitacoes_pendentes = []
    if u.role in ('admin', 'editor'):
        eventos_pendentes = _eventos_pendentes_ocultar()
        solicitacoes_pendentes = Course.query.filter_by(via_formulario=True, status='em_edicao')\
            .order_by(Course.created_at.desc()).all()

    # Lembretes mensais fixos e pessoais — só os do próprio usuário, só os
    # que estão pendentes (ver _lembrete_pendencia). Não somem sozinhos: só
    # saem daqui quando a própria pessoa clica em "Já fiz isso".
    lembretes_ativos = [
        d for l in LembreteFixo.query.filter_by(user_id=u.id, ativo=True).order_by(LembreteFixo.dia_mes).all()
        for d in [_lembrete_para_exibir(l)] if d['status']
    ]

    # Avisos manuais de Demanda do Calendário — visíveis pra quem enxerga o
    # Calendário, exceto quem já dispensou (clicou pra sumir) este aviso.
    alertas_demandas_ativos = []
    if u.can_view_calendario():
        dispensados = {row.demanda_id for row in DemandaAlertaDispensa.query.filter_by(user_id=u.id).all()}
        alertas_demandas_ativos = [
            d for d in Demanda.query.filter_by(alerta_ativo=True).order_by(Demanda.data_fim).all()
            if d.id not in dispensados
        ]

    # Reuniões de hoje/amanhã puxadas do link ICS da agenda pessoal
    # (Outlook/Google) — some sozinha quando o dia passa, não precisa
    # check-in (diferente do lembrete fixo, que é recorrente). As minhas
    # aparecem sempre; as de quem marcou "Todo mundo vê" aparecem também,
    # marcadas com o nome do dono (ver agenda_ics_visibilidade).
    reunioes_ativas = list(_reunioes_hoje_amanha(u))
    outros_com_agenda_publica = User.query.filter(
        User.id != u.id, User.agenda_ics_url.isnot(None), User.agenda_ics_visibilidade == 'todos',
    ).all()
    for outro in outros_com_agenda_publica:
        for ev in _reunioes_hoje_amanha(outro):
            reunioes_ativas.append({**ev, 'dono': nome_exibicao(outro)})
    reunioes_ativas.sort(key=lambda r: (r['dias_para'], r['hora'] or ''))

    return {
        'notif_count': len(pendentes),
        'notif_list': notif_list,
        'admin_finalizado': admin_finalizado,
        'admin_finalizado_count': len(admin_finalizado),
        'eventos_pendentes': eventos_pendentes,
        'eventos_pendentes_count': len(eventos_pendentes),
        'solicitacoes_pendentes': solicitacoes_pendentes,
        'solicitacoes_pendentes_count': len(solicitacoes_pendentes),
        'can_cupons': u.can_manage_cupons(),
        'can_reembolsos': u.can_manage_reembolsos(),
        'can_historico': u.can_view_historico(),
        'can_erp_moodle': u.can_view_erp_moodle(),
        'somente_erp_moodle': False,
        'ferramentas_tools': ExternalTool.query.order_by(ExternalTool.ordem, ExternalTool.label).all() if u.can_view_ferramentas() else [],
        'sidebar_section_order': _sidebar_section_order(),
        'modulos_ordem': _modulos_ordem(),
        'can_cursos': u.can_view_cursos(),
        'can_matrizes': u.can_view_matrizes(),
        'can_banco_disciplinas': u.can_view_banco_disciplinas(),
        'can_ia_assistente': u.can_view_ia_assistente(),
        'can_ferramentas': u.can_view_ferramentas(),
        'can_pagamentos_terceiros': u.can_manage_pagamentos_terceiros(),
        'can_opcoes_curso': u.can_manage_opcoes_curso(),
        'can_mural': u.can_view_mural(),
        'can_formularios': u.can_view_formularios(),
        'can_calendario': u.can_view_calendario(),
        'lembretes_ativos': lembretes_ativos,
        'alertas_demandas_ativos': alertas_demandas_ativos,
        'reunioes_ativas': reunioes_ativas,
    }

# ─── AUTH ROUTES ───────────────────────────────────────────────────────────────

def _home_redirect(u):
    """Pra onde mandar a pessoa depois de logar/acessar '/': contas restritas
    ao ERP Moodle (equipe externa) caem direto lá, sem passar pelo dashboard
    do INOVA que elas não têm acesso a ver."""
    if u and u.is_restrito_erp_moodle():
        return redirect(url_for('erp_moodle'))
    return redirect(url_for('dashboard'))

@app.route('/')
def index():
    if 'user_id' in session:
        return _home_redirect(User.query.get(session['user_id']))
    return redirect(url_for('login'))

@app.route('/login', methods=['GET','POST'])
@limiter.limit("10 per minute", methods=['POST'])
def login():
    if request.method == 'POST':
        identificador = request.form.get('email', '').strip().lower()
        # Aceita e-mail institucional (novo padrão) ou nome de usuário (contas
        # antigas ainda sem e-mail cadastrado) até que todas as contas migrem.
        u = User.query.filter(
            db.or_(db.func.lower(User.email) == identificador,
                   db.func.lower(User.username) == identificador)
        ).first()
        if u and check_pw(u.password, request.form['password']):
            if not u.password.startswith(('pbkdf2:', 'scrypt:')):
                u.password = hash_pw(request.form['password'])
            # Se ficou ausente por um tempo, avisa a própria pessoa ao voltar
            # (calcula ANTES de sobrescrever ultimo_login com o login de agora).
            if u.ultimo_login and (datetime.utcnow() - u.ultimo_login).days >= DIAS_INATIVIDADE:
                dias_fora = (datetime.utcnow() - u.ultimo_login).days
                flash(f'Bem-vindo(a) de volta! Fazia {dias_fora} dia(s) que você não entrava no sistema.', 'success')
            u.ultimo_login = datetime.utcnow()
            db.session.commit()
            session.permanent = True
            session['user_id'] = u.id
            session['username'] = u.username
            session['role'] = u.role
            log_action(u.id, u.username, 'login', 'user', u.id)
            return _home_redirect(u)
        flash('Usuário ou senha incorretos.', 'danger')
    return render_template('login.html', demo_link_ativo=bool(_demo_publico_user_id()))

def _demo_publico_user_id():
    setting = AppSetting.query.get('demo_publico_user_id')
    return int(setting.value) if setting and setting.value else None

@app.route('/demonstracao')
@limiter.limit("30 per minute")
def acesso_demonstracao():
    """Link público de vitrine — entra direto, sem pedir senha, na conta
    que o admin escolheu explicitamente em Admin → Dados Fictícios (nunca
    detecta sozinho). Só funciona se essa conta existir, ainda estiver
    marcada como 'Conta de demonstração' e o admin não tiver desligado o
    link. É seguro ser público porque essa conta já não consegue criar/
    editar/excluir nada nem emitir relatório (bloqueado globalmente em
    restringir_conta_demo) — o pior que dá pra fazer é navegar vendo dado
    fictício."""
    uid = _demo_publico_user_id()
    conta = User.query.get(uid) if uid else None
    if not conta or not conta.is_conta_demo():
        abort(404)
    session.permanent = True
    session['user_id'] = conta.id
    session['username'] = conta.username
    session['role'] = conta.role
    return _home_redirect(conta)

@app.route('/esqueci-senha', methods=['GET','POST'])
@limiter.limit("5 per minute", methods=['POST'])
def esqueci_senha():
    if request.method == 'POST':
        email = request.form.get('email', '').strip().lower()
        u = User.query.filter(db.func.lower(User.email) == email).first()
        if u:
            token = _reset_senha_serializer().dumps(u.id)
            link = url_for('resetar_senha', token=token, _external=True)
            corpo = (
                f'Olá {u.nome or u.username},\n\n'
                f'Recebemos um pedido para redefinir sua senha no Gestor Acadêmico.\n'
                f'Clique no link abaixo para escolher uma nova senha (válido por 1 hora):\n\n'
                f'{link}\n\n'
                f'Se você não pediu essa redefinição, pode ignorar este e-mail.'
            )
            enviar_email(u.email, 'Redefinição de senha — Gestor Acadêmico', corpo)
        # Mensagem sempre igual, exista ou não o e-mail — evita confirmar pra quem
        # está tentando descobrir quais e-mails têm conta no sistema.
        flash('Se esse e-mail estiver cadastrado, enviamos um link de redefinição.', 'success')
        return redirect(url_for('login'))
    return render_template('esqueci_senha.html')

@app.route('/resetar-senha/<token>', methods=['GET','POST'])
def resetar_senha(token):
    try:
        user_id = _reset_senha_serializer().loads(token, max_age=3600)
    except (BadSignature, SignatureExpired):
        flash('Link inválido ou expirado. Solicite a redefinição novamente.', 'danger')
        return redirect(url_for('esqueci_senha'))
    u = User.query.get(user_id)
    if not u:
        flash('Usuário não encontrado.', 'danger')
        return redirect(url_for('esqueci_senha'))
    if request.method == 'POST':
        nova = request.form.get('nova_senha', '')
        confirmar = request.form.get('confirmar_senha', '')
        if len(nova) < 8:
            flash('A nova senha precisa ter pelo menos 8 caracteres.', 'danger')
        elif nova != confirmar:
            flash('As senhas não coincidem.', 'danger')
        else:
            u.password = hash_pw(nova)
            u.must_change_password = False
            db.session.commit()
            log_action(u.id, u.username, 'resetar_senha_email', 'user', u.id)
            flash('Senha redefinida com sucesso! Faça login com a nova senha.', 'success')
            return redirect(url_for('login'))
    return render_template('resetar_senha.html', token=token)

@app.route('/logout')
def logout():
    session.clear()
    return redirect(url_for('login'))

# ─── FORMULÁRIO PÚBLICO DE SOLICITAÇÃO (sem login) ──────────────────────────
# Link pra mandar pra quem pede criação de evento — preenche e cai direto
# como um curso rascunho (em_edicao) no sistema, sem precisar de conta.

@app.route('/solicitar/evento', methods=['GET', 'POST'])
@limiter.limit("8 per hour", methods=['POST'])
def solicitar_evento():
    if request.method == 'POST':
        d = request.form
        nome = d.get('nome', '').strip()
        if not nome:
            flash('Preencha ao menos o nome do evento.', 'danger')
            return render_template('solicitar_evento.html')

        tem_cupom = d.get('tem_cupom', '')
        cupom_pct = d.get('cupom_percentual', '').strip()
        cronograma = d.get('cronograma', '').strip()
        data_certificado = d.get('data_certificado', '').strip()
        banco_questoes = d.get('banco_questoes', '')

        obs_partes = [
            f'Solicitado via formulário público em {datetime.now().strftime("%d/%m/%Y %H:%M")}.',
            f'Solicitante: {d.get("solicitante_nome","").strip() or "—"} ({d.get("solicitante_contato","").strip() or "—"})',
            '',
            f'Cupom: {"Sim — " + cupom_pct + "%" if tem_cupom == "sim" else ("Não" if tem_cupom == "nao" else "—")}',
            f'Data prevista p/ emissão do certificado: {data_certificado or "—"}',
            f'Banco de questões: {"Sim" if banco_questoes == "sim" else ("Não" if banco_questoes == "nao" else "—")}',
        ]
        if cronograma:
            obs_partes += ['', 'Cronograma informado:', cronograma]

        extra = {}
        capa_url = d.get('capa_url', '').strip()
        if capa_url:
            extra['imagens'] = [{'descricao': 'Capa sugerida pelo solicitante', 'url': capa_url}]

        c = Course(
            nome=nome, tipo='evento', status='em_edicao',
            horas=d.get('horas', '').strip(), valor=d.get('valor', '').strip(),
            data_finalizacao=_parse_data_form(d.get('prazo_entrega', '')),
            link_imagem=capa_url, obs='\n'.join(obs_partes),
            extra_data=json.dumps(extra, ensure_ascii=False),
            via_formulario=True,
        )
        db.session.add(c)
        db.session.commit()
        log_action(None, d.get('solicitante_nome', '').strip() or 'solicitação externa',
                   'criar_via_formulario', 'course', c.id, c.nome)
        return render_template('solicitar_evento.html', enviado=True)
    return render_template('solicitar_evento.html')

@app.route('/minha-conta', methods=['GET','POST'])
@login_required
def minha_conta():
    u = User.query.get(session['user_id'])
    if request.method == 'POST':
        if not u.can_change_own_password():
            flash('Você não tem permissão para alterar sua própria senha. Fale com um administrador.', 'danger')
            return redirect(url_for('minha_conta'))
        senha_atual = request.form.get('senha_atual', '')
        nova = request.form.get('nova_senha', '')
        confirmar = request.form.get('confirmar_senha', '')
        if not check_pw(u.password, senha_atual):
            flash('Senha atual incorreta.', 'danger')
        elif len(nova) < 8:
            flash('A nova senha precisa ter pelo menos 8 caracteres.', 'danger')
        elif nova != confirmar:
            flash('As senhas novas não coincidem.', 'danger')
        else:
            u.password = hash_pw(nova)
            u.must_change_password = False
            db.session.commit()
            log_action(u.id, u.username, 'trocar_senha', 'user', u.id)
            flash('Senha alterada com sucesso!', 'success')
            return redirect(url_for('dashboard'))
    try:
        whatsapp_prefs = json.loads(u.whatsapp_prefs or '{}')
    except (ValueError, TypeError):
        whatsapp_prefs = {}
    return render_template('minha_conta.html', u=u, whatsapp_prefs=whatsapp_prefs)

@app.route('/minha-conta/whatsapp', methods=['POST'])
@login_required
def minha_conta_whatsapp():
    """Telefone + apikey do CallMeBot, opcionais — usados só se a pessoa
    marcar 'avisar por WhatsApp também' em algum lembrete/aviso. Sem os
    dois cadastrados, esse aviso simplesmente não é enviado (ver
    _enviar_avisos_whatsapp_pendentes)."""
    u = User.query.get(session['user_id'])
    telefone = (request.form.get('telefone_whatsapp') or '').strip()
    apikey = (request.form.get('whatsapp_apikey') or '').strip()
    u.telefone_whatsapp = telefone[:30] or None
    u.whatsapp_apikey = apikey[:50] or None
    db.session.commit()
    flash('WhatsApp atualizado!', 'success')
    return redirect(_voltar_seguro(url_for('calendario', aba='alertas')))

@app.route('/calendario/agenda-ics', methods=['POST'])
@perm_check('can_view_calendario')
def calendario_agenda_ics():
    """Link secreto ICS da agenda pessoal (Outlook/Google) — reuniões de
    hoje/amanhã passam a aparecer no aviso do topo (ver
    _reunioes_hoje_amanha). Limpa o cache antigo pra já buscar de novo com
    o link certo na próxima página."""
    u = User.query.get(session['user_id'])
    url = (request.form.get('agenda_ics_url') or '').strip()
    u.agenda_ics_url = url or None
    u.agenda_ics_visibilidade = 'todos' if request.form.get('agenda_ics_visibilidade') == 'todos' else 'pessoal'
    u.agenda_cache_json = None
    u.agenda_cache_em = None
    db.session.commit()
    flash('Agenda atualizada!', 'success')
    return redirect(_voltar_seguro(url_for('calendario', aba='alertas')))

@app.route('/calendario/agenda-ics/testar', methods=['POST'])
@perm_check('can_view_calendario')
def calendario_agenda_ics_testar():
    """Busca o link ICS na hora (ignora o cache de 20 min) e devolve o que
    encontrou, ou o erro exato — usado pelo botão "Testar agora", pra
    diagnosticar sem esperar o cache nem me passar o link."""
    u = User.query.get(session['user_id'])
    if not u.agenda_ics_url:
        return jsonify({'ok': False, 'erro': 'Cadastre o link da agenda antes de testar.'})
    try:
        eventos = _buscar_reunioes_ics(u.agenda_ics_url, date.today())
        u.agenda_cache_json = json.dumps(eventos, ensure_ascii=False)
        u.agenda_cache_em = datetime.utcnow()
        db.session.commit()
        return jsonify({'ok': True, 'eventos': eventos})
    except Exception as e:
        return jsonify({'ok': False, 'erro': str(e)[:400]})

@app.route('/minha-conta/whatsapp-prefs', methods=['POST'])
@admin_required
def minha_conta_whatsapp_prefs():
    """Só admin escolhe o que quer receber no WhatsApp fora dos lembretes e
    avisos de Demanda (esses dois já têm opt-in próprio, em cada um)."""
    u = User.query.get(session['user_id'])
    prefs = {
        'disciplinas_concluidas': request.form.get('pref_disciplinas_concluidas') == 'on',
        'erros_plataforma': request.form.get('pref_erros_plataforma') == 'on',
        'sino_diario': request.form.get('pref_sino_diario') == 'on',
    }
    u.whatsapp_prefs = json.dumps(prefs)
    db.session.commit()
    flash('Preferências de WhatsApp atualizadas!', 'success')
    return redirect(_voltar_seguro(url_for('calendario', aba='alertas')))

# ─── DASHBOARD ─────────────────────────────────────────────────────────────────

@app.route('/dashboard')
@login_required
def dashboard():
    from sqlalchemy import or_ as sql_or, func as sql_func

    u = User.query.get(session['user_id'])
    # Conta de demonstração vê o dashboard como admin (visão agregada da
    # equipe) — só pra exibição/consulta; a rota é GET-only e o bloqueio
    # real de criar/editar/excluir continua em restringir_conta_demo. Nome
    # de responsável é trocado por fictício logo abaixo (equipe_exibicao),
    # nunca aparece nome de usuário real pra essa conta.
    is_admin = u.role == 'admin' or u.is_conta_demo()
    filtro_ins = request.args.get('insersor', '')

    # Para não-admins, aplica filtro automático pelo nome do próprio usuário
    def _ins_filter(q, nome):
        n = nome.lower()
        n_norm = _norm_name(nome)
        inicial = next((k for k, v in INICIAIS_INSERCAO.items() if v == n_norm), None)
        conds = [
            sql_func.lower(Course.insersor) == n,
            sql_func.lower(Course.insersor).like(f'{n},%'),
            sql_func.lower(Course.insersor).like(f'%,{n}'),
            sql_func.lower(Course.insersor).like(f'%,{n},%'),
        ]
        if inicial:
            i = inicial.lower()
            conds += [
                sql_func.lower(Course.insersor) == i,
                sql_func.lower(Course.insersor).like(f'{i},%'),
                sql_func.lower(Course.insersor).like(f'%,{i}'),
                sql_func.lower(Course.insersor).like(f'%,{i},%'),
            ]
        return q.filter(sql_or(*conds))

    q_base = Course.query
    if is_admin and filtro_ins:
        q_base = _ins_filter(q_base, filtro_ins)
    elif not is_admin:
        q_base = _ins_filter(q_base, u.username)

    total      = q_base.count()
    ativos     = q_base.filter_by(status='ativo').count()
    em_edicao  = q_base.filter_by(status='em_edicao').count()
    desc       = q_base.filter_by(status='descontinuado').count()
    ocultos    = q_base.filter_by(status='oculto').count()
    finalizado = q_base.filter_by(status='finalizado').count()

    por_tipo = db.session.query(Course.tipo, db.func.count(Course.id))\
                         .group_by(Course.tipo).all()
    pos_count = next((c for t, c in por_tipo if t == 'pos'), 0)

    if is_admin:
        recentes = AuditLog.query.order_by(AuditLog.timestamp.desc()).limit(10).all()
    else:
        recentes = AuditLog.query.filter(
            sql_func.lower(AuditLog.username) == u.username.lower()
        ).order_by(AuditLog.timestamp.desc()).limit(10).all()

    ultimo_bk = BackupRecord.query.order_by(BackupRecord.created_at.desc()).first()

    # Nome de responsável exibido — pra conta de demonstração, troca cada
    # nome real da equipe pelo fictício correspondente (mesmo mapa usado em
    # "Gerar Dados Fictícios", então bate com o que já está gravado em
    # Course.insersor). Pra todo mundo, é só a lista real mesmo.
    equipe_exibicao = responsaveis_atuais()
    if u.is_conta_demo():
        _mapa_demo = _mapa_nomes_ficticios()
        equipe_exibicao = [_mapa_demo.get(_norm_name(n), n) for n in equipe_exibicao]

    # Andamento por insersor: pendentes e concluídas por pessoa
    # Para não-admins: apenas a própria linha
    equipe = [n.upper() for n in equipe_exibicao] if is_admin else [u.username.upper()]

    stats_map = {nome.upper(): {'pendentes': 0, 'concluidas': 0, 'total': 0} for nome in equipe}

    raw_disc = db.session.query(Course.insersor, Discipline.plataforma_ok, db.func.count(Discipline.id))\
        .join(Discipline, Discipline.course_id == Course.id)\
        .filter(Course.insersor != None, Course.insersor != '')\
        .group_by(Course.insersor, Discipline.plataforma_ok).all()

    for ins_field, ok, qtd in raw_disc:
        for parte in ins_field.split(','):
            p = parte.strip()
            p_norm = _norm_name(p)
            # Expande inicial única (ex: 'S' → 'STEFANYE')
            if len(p) == 1:
                p_norm = INICIAIS_INSERCAO.get(p.upper(), p_norm)
            for canonical in equipe:
                if p_norm == _norm_name(canonical):
                    stats_map[canonical.upper()]['total'] += qtd
                    if ok:
                        stats_map[canonical.upper()]['concluidas'] += qtd
                    else:
                        stats_map[canonical.upper()]['pendentes'] += qtd
                    break

    pend_por_ins = sorted(
        [(nome, v['pendentes'], v['concluidas'], v['total'])
         for nome, v in stats_map.items() if v['total'] > 0 or is_admin],
        key=lambda x: x[1], reverse=True
    )

    insersores = equipe_exibicao if is_admin else []

    # Total real de disciplinas pendentes (conta também cursos sem insersor
    # atribuído — o quadro por pessoa acima não os contabiliza, porque não
    # tem a quem atribuir a linha).
    ids_base = [r[0] for r in q_base.with_entities(Course.id).all()]
    discs_pendentes_lista = []
    total_disc_pendentes = 0
    if ids_base:
        total_disc_pendentes = Discipline.query.filter(
            Discipline.course_id.in_(ids_base), Discipline.plataforma_ok == False
        ).count()
        discs_pendentes_lista = (db.session.query(Discipline, Course)
            .join(Course, Discipline.course_id == Course.id)
            .filter(Discipline.course_id.in_(ids_base), Discipline.plataforma_ok == False)
            .order_by(Course.nome, Discipline.ordem)
            .limit(10).all())

    # Card: cursos por responsável (insersor)
    cursos_ins_stats = []
    nomes_ins = equipe_exibicao if is_admin else [u.username]
    for ins_nome in nomes_ins:
        q_ins = _ins_filter(Course.query, ins_nome)
        total_ins = q_ins.count()
        if not is_admin and total_ins == 0:
            continue
        ativos_ins   = q_ins.filter_by(status='ativo').count()
        em_ed_ins    = q_ins.filter_by(status='em_edicao').count()
        ids_ins = [r[0] for r in q_ins.with_entities(Course.id).all()]
        pend_disc_ins = Discipline.query.filter(
            Discipline.course_id.in_(ids_ins),
            Discipline.plataforma_ok == False
        ).count() if ids_ins else 0
        cursos_ins_stats.append({
            'nome': ins_nome,
            'total': total_ins,
            'ativos': ativos_ins,
            'em_edicao': em_ed_ins,
            'pend_disc': pend_disc_ins,
        })

    # Série mensal (últimos 6 meses) de cursos cadastrados, pro gráfico do painel —
    # respeita o mesmo filtro de insersor usado nos KPIs acima.
    def _primeiro_dia_mes(d, meses_atras):
        m = d.month - meses_atras
        y = d.year
        while m <= 0:
            m += 12
            y -= 1
        while m > 12:
            m -= 12
            y += 1
        return datetime(y, m, 1)

    hoje = datetime.utcnow()
    serie_mensal = []
    for i in range(5, -1, -1):
        ini = _primeiro_dia_mes(hoje, i)
        fim = _primeiro_dia_mes(hoje, i - 1)
        qtd = q_base.filter(Course.created_at >= ini, Course.created_at < fim).count()
        serie_mensal.append({'label': ini.strftime('%b'), 'qtd': qtd})

    widgets_ordem, widgets_ocultos, widgets_tamanhos, widgets_posicoes, widgets_alturas_salvas = get_dashboard_prefs(u)
    todos_usuarios = User.query.order_by(User.username).all() if u.role == 'admin' else []
    # Padrão global (definido pelo admin em /admin/visibilidade) de quais
    # widgets ficam disponíveis pra quem não é admin — admin sempre vê tudo.
    widgets_liberados = _widgets_dashboard_visiveis() if not is_admin else {}

    # Widget "Cursos sem responsável" — cursos com o campo insersor vazio,
    # ninguém cuidando deles ainda.
    q_sem_resp = Course.query.filter(sql_or(Course.insersor == None, Course.insersor == ''))
    total_sem_resp = q_sem_resp.count()
    cursos_sem_resp = q_sem_resp.order_by(Course.nome).limit(8).all()

    # Widget "Reembolsos pendentes" — só pra quem tem permissão de reembolsos.
    pode_ver_reembolsos = u.can_manage_reembolsos()
    reembolsos_pend_qtd = 0
    reembolsos_pend_valor = 0
    if pode_ver_reembolsos:
        reembolsos_pend_qtd = Refund.query.filter_by(concluido_manual=False).count()
        reembolsos_pend_valor = db.session.query(
            db.func.coalesce(db.func.sum(Refund.valor), 0)
        ).filter_by(concluido_manual=False).scalar()

    # Widget "Calendário — Disciplinas por Módulo" — total pendente (some
    # cai conforme a equipe registra o andamento) e a quantidade em cada
    # etapa da inserção, até liberada no Moodle. Arquivadas ficam de fora.
    _disc_modulo_ativas = DisciplinaModulo.query.filter_by(arquivado=False)
    disc_modulo_total = _disc_modulo_ativas.count()
    disc_modulo_pendentes = _disc_modulo_ativas.filter(
        ~DisciplinaModulo.status.in_(['liberada_moodle', 'liberada_inova'])).count()
    disc_modulo_por_status = dict(
        db.session.query(DisciplinaModulo.status, db.func.count(DisciplinaModulo.id))
        .filter(DisciplinaModulo.arquivado == False)
        .group_by(DisciplinaModulo.status).all()
    )

    return render_template('dashboard.html',
        total=total, ativos=ativos, em_edicao=em_edicao, desc=desc,
        ocultos=ocultos, finalizado=finalizado,
        por_tipo=por_tipo, pos_count=pos_count, recentes=recentes,
        ultimo_bk=ultimo_bk, pend_por_ins=pend_por_ins,
        insersores=insersores, filtro_ins=filtro_ins,
        is_admin=is_admin, usuario_atual=u, dados_ficticios_ativos=_dados_ficticios_ativos(),
        cursos_ins_stats=cursos_ins_stats, serie_mensal=serie_mensal,
        total_disc_pendentes=total_disc_pendentes, discs_pendentes_lista=discs_pendentes_lista,
        widgets_ordem=widgets_ordem, widgets_ocultos=widgets_ocultos, widgets_tamanhos=widgets_tamanhos,
        widgets_posicoes=widgets_posicoes, widgets_alturas_salvas=widgets_alturas_salvas,
        widgets_liberados=widgets_liberados,
        dashboard_widgets=DASHBOARD_WIDGETS, todos_usuarios=todos_usuarios,
        total_sem_resp=total_sem_resp, cursos_sem_resp=cursos_sem_resp,
        pode_ver_reembolsos=pode_ver_reembolsos,
        reembolsos_pend_qtd=reembolsos_pend_qtd, reembolsos_pend_valor=reembolsos_pend_valor,
        disc_modulo_total=disc_modulo_total, disc_modulo_pendentes=disc_modulo_pendentes,
        disc_modulo_por_status=disc_modulo_por_status, STATUS_DISC_MODULO_LABEL=STATUS_DISC_MODULO_LABEL)

@app.route('/dashboard/prefs', methods=['GET'])
@login_required
def dashboard_prefs_obter():
    """Devolve a ordem/visibilidade de widgets salva — da própria conta, ou
    (só admin) da conta de outro usuário indicada em ?user_id=."""
    u = User.query.get(session['user_id'])
    target_id = request.args.get('user_id', type=int)
    if target_id and target_id != u.id:
        if u.role != 'admin':
            return jsonify({'ok': False, 'erro': 'Sem permissão.'}), 403
        alvo = User.query.get_or_404(target_id)
    else:
        alvo = u
    ordem, ocultos, tamanhos, posicoes, alturas = get_dashboard_prefs(alvo)
    return jsonify({'ok': True, 'order': ordem, 'hidden': list(ocultos), 'sizes': tamanhos,
                     'positions': posicoes, 'heights': alturas})

@app.route('/dashboard/prefs', methods=['POST'])
@login_required
def dashboard_prefs_salvar():
    """Salva a ordem/visibilidade/tamanho/posição (linha e coluna livres) dos
    widgets — da própria conta, ou (só admin) da conta de outro usuário
    indicada em user_id no corpo da requisição."""
    u = User.query.get(session['user_id'])
    data = request.json or {}
    target_id = data.get('user_id')
    if target_id and int(target_id) != u.id:
        if u.role != 'admin':
            return jsonify({'ok': False, 'erro': 'Sem permissão.'}), 403
        alvo = User.query.get_or_404(int(target_id))
    else:
        alvo = u
    ordem_in = data.get('order', [])
    ocultos_in = data.get('hidden', [])
    tamanhos_in = data.get('sizes', {})
    alturas_in = data.get('heights', {})
    posicoes_in = data.get('positions', {})
    if (not isinstance(ordem_in, list) or not isinstance(ocultos_in, list)
            or not isinstance(tamanhos_in, dict) or not isinstance(alturas_in, dict)
            or not isinstance(posicoes_in, dict)):
        return jsonify({'ok': False, 'erro': 'Formato inválido.'}), 400
    ordem = [w for w in ordem_in if w in _DASHBOARD_WIDGET_IDS]
    ocultos = [w for w in ocultos_in if w in _DASHBOARD_WIDGET_IDS]
    tamanhos = {}
    for wid, tam in tamanhos_in.items():
        if wid in _DASHBOARD_WIDGET_IDS:
            try:
                tam = int(tam)
            except (TypeError, ValueError):
                continue
            if 1 <= tam <= 4:
                tamanhos[wid] = tam
    alturas = {}
    for wid, alt in alturas_in.items():
        if wid in _DASHBOARD_WIDGET_IDS:
            try:
                alt = int(alt)
            except (TypeError, ValueError):
                continue
            if 1 <= alt <= 30:
                alturas[wid] = alt
    posicoes = {}
    for wid, pos in posicoes_in.items():
        if wid not in _DASHBOARD_WIDGET_IDS or not isinstance(pos, dict):
            continue
        try:
            r, c = int(pos.get('row')), int(pos.get('col'))
        except (TypeError, ValueError):
            continue
        if 0 <= r <= 200 and 0 <= c <= 3:
            posicoes[wid] = {'row': r, 'col': c}
    alvo.dashboard_prefs = json.dumps({'order': ordem, 'hidden': ocultos, 'sizes': tamanhos,
                                        'heights': alturas,
                                        'positions': posicoes, 'positions_versao': DASHBOARD_POSITIONS_VERSAO})
    db.session.commit()
    return jsonify({'ok': True})

@app.route('/dashboard/notas', methods=['POST'])
@login_required
def dashboard_notas_salvar():
    """Salva o texto do widget "Notas rápidas" — sempre da própria conta,
    não existe versão pra admin editar a nota de outra pessoa."""
    u = User.query.get(session['user_id'])
    texto = (request.json or {}).get('texto', '')
    if not isinstance(texto, str):
        return jsonify({'ok': False, 'erro': 'Formato inválido.'}), 400
    u.notas_pessoais = texto[:4000]
    db.session.commit()
    return jsonify({'ok': True})

# ─── COURSES ───────────────────────────────────────────────────────────────────

@app.route('/cursos')
@perm_check('can_view_cursos')
def cursos():
    tipo      = request.args.get('tipo','')
    area      = request.args.get('area','')
    status    = request.args.get('status','')
    busca     = request.args.get('q','')
    insersor  = request.args.get('insersor','')
    horas_min = request.args.get('horas_min','')
    horas_max = request.args.get('horas_max','')
    lista = _build_cursos_query(tipo, area, status, busca, insersor, horas_min, horas_max)
    areas  = AREAS_VALIDAS
    insersores = [u.username for u in User.query.order_by(User.username).all()]
    contagem_status = _contagem_cursos_por_status(tipo, area, busca)
    venda_opcoes = VendaModalidadeOpcao.query.order_by(VendaModalidadeOpcao.ordem).all()
    return render_template('cursos.html', cursos=lista, areas=areas, insersores=insersores,
                           filtro_tipo=tipo, filtro_area=area, filtro_status=status,
                           contagem_status=contagem_status, venda_opcoes=venda_opcoes,
                           filtro_insersor=insersor, busca=busca,
                           filtro_horas_min=horas_min, filtro_horas_max=horas_max)

@app.route('/cursos/<int:id>/venda-modalidade', methods=['POST'])
@editor_required
def curso_venda_modalidade(id):
    """Atualiza só a modalidade de venda (Nenhum/Link/Site/...) direto pela
    listagem — sem precisar abrir Editar Curso. Pensado pra eventos, que
    costumam mudar esse campo com frequência."""
    c = Course.query.get_or_404(id)
    data = request.get_json(silent=True) or {}
    valor = (data.get('venda_modalidade') or '').strip()
    if valor:
        opcoes_validas = {o.label for o in VendaModalidadeOpcao.query.all()}
        if valor not in opcoes_validas:
            return jsonify({'ok': False, 'erro': 'Opção inválida.'}), 400
    c.venda_modalidade = valor or None
    db.session.commit()
    log_action(session['user_id'], session['username'], 'editar', 'course', c.id,
               f'Venda por: "{valor or "Nenhum"}"')
    return jsonify({'ok': True, 'venda_modalidade': c.venda_modalidade})


def _contagem_cursos_por_status(tipo, area, busca):
    """Quantos cursos existem em cada status, respeitando tipo/área/busca
    atuais (os mesmos filtros que os chips de status preservam ao trocar
    de aba) — usado pro contador ao lado de cada chip em /cursos."""
    q = db.session.query(Course.status, db.func.count(Course.id))
    if tipo:  q = q.filter(Course.tipo == tipo)
    if area:  q = q.filter(Course.area == area)
    if busca: q = q.filter(Course.nome.ilike(f'%{busca}%'))
    contagem = dict(q.group_by(Course.status).all())
    contagem[''] = sum(contagem.values())
    return contagem

def _build_cursos_query(tipo, area, status, busca, insersor, horas_min='', horas_max=''):
    from sqlalchemy import or_ as sql_or, func as sql_func
    q = Course.query
    if tipo:     q = q.filter_by(tipo=tipo)
    if area:     q = q.filter_by(area=area)
    if status:   q = q.filter_by(status=status)
    if insersor:
        ins = insersor.lower()
        q = q.filter(sql_or(
            sql_func.lower(Course.insersor) == ins,
            sql_func.lower(Course.insersor).like(f'{ins},%'),
            sql_func.lower(Course.insersor).like(f'%,{ins}'),
            sql_func.lower(Course.insersor).like(f'%,{ins},%'),
        ))
    if busca:    q = q.filter(Course.nome.ilike(f'%{busca}%'))
    lista = q.order_by(Course.created_at.desc(), Course.id.desc()).all()

    # "horas" é texto livre na planilha (ex.: "180", "20h", "-"), então o
    # filtro por faixa é feito em Python extraindo o número de cada curso.
    if horas_min or horas_max:
        import re as _re_h
        try: hmin = int(horas_min) if horas_min else None
        except ValueError: hmin = None
        try: hmax = int(horas_max) if horas_max else None
        except ValueError: hmax = None
        def _horas_num(c):
            if not c.horas: return None
            m = _re_h.search(r'\d+', str(c.horas))
            return int(m.group()) if m else None
        def _dentro_faixa(c):
            n = _horas_num(c)
            if n is None: return False
            if hmin is not None and n < hmin: return False
            if hmax is not None and n > hmax: return False
            return True
        lista = [c for c in lista if _dentro_faixa(c)]

    return lista

@app.route('/cursos/status-em-lote', methods=['POST'])
@perm_check('can_view_cursos')
def cursos_status_em_lote():
    """Muda o status (ativo/em edição/finalizado/arquivado/oculto/inativo) de
    vários cursos de uma vez — só admin (só altera o campo status, nenhum
    curso, disciplina ou outro dado é apagado)."""
    if session.get('role') != 'admin':
        return jsonify({'ok': False, 'erro': 'Somente administradores podem realizar ações em lote.'}), 403
    data = request.json or {}
    ids = data.get('ids', [])
    novo_status = data.get('status', '')
    if novo_status not in ('ativo', 'em_edicao', 'finalizado', 'descontinuado', 'oculto', 'inativo'):
        return jsonify({'ok': False, 'erro': 'Status inválido.'}), 400
    if not ids:
        return jsonify({'ok': False, 'erro': 'Nenhum curso selecionado.'}), 400

    cursos_sel = Course.query.filter(Course.id.in_(ids)).all()
    total = 0
    for c in cursos_sel:
        if c.status != novo_status:
            c.status = novo_status
            total += 1
    db.session.commit()
    if total:
        log_action(session['user_id'], session['username'], 'status_em_lote', 'course', None,
                   f'{total} curso(s) -> status={novo_status}')
    return jsonify({'ok': True, 'total': total})

@app.route('/cursos/editar-em-lote', methods=['POST'])
@editor_required
@perm_check('can_view_cursos')
def cursos_editar_em_lote():
    """Aplica Venda por / Valor / Horas / Área em vários cursos de uma vez. Só os
    campos que vierem no JSON são alterados — marcar só 1 deles não mexe
    nos outros, pra não zerar campo por engano."""
    data = request.json or {}
    ids = data.get('ids', [])
    if not ids:
        return jsonify({'ok': False, 'erro': 'Nenhum curso selecionado.'}), 400
    campos = [c for c in ('venda_modalidade', 'valor', 'horas', 'area') if c in data]
    if not campos:
        return jsonify({'ok': False, 'erro': 'Marque pelo menos um campo pra aplicar.'}), 400

    if 'area' in data:
        area_val = (data.get('area') or '').strip()
        if area_val and area_val not in AREAS_VALIDAS:
            return jsonify({'ok': False, 'erro': f'Área inválida: {area_val}.'}), 400

    if 'venda_modalidade' in data:
        # Aceita mais de uma opção marcada, separadas por vírgula (ex: "Link, Site")
        vm_itens = [v.strip() for v in (data.get('venda_modalidade') or '').split(',') if v.strip()]
        if vm_itens:
            opcoes_validas = {o.label for o in VendaModalidadeOpcao.query.all()}
            invalidas = [v for v in vm_itens if v not in opcoes_validas]
            if invalidas:
                return jsonify({'ok': False, 'erro': f'Opção de "Venda por" inválida: {", ".join(invalidas)}.'}), 400

    cursos_sel = Course.query.filter(Course.id.in_(ids)).all()
    if not cursos_sel:
        return jsonify({'ok': False, 'erro': 'Nenhum curso encontrado.'}), 400

    resumo = []
    for c in cursos_sel:
        if 'venda_modalidade' in data:
            c.venda_modalidade = (data.get('venda_modalidade') or '').strip() or None
        if 'valor' in data:
            c.valor = (data.get('valor') or '').strip()
        if 'horas' in data:
            c.horas = (data.get('horas') or '').strip()
        if 'area' in data:
            c.area = (data.get('area') or '').strip() or None
    if 'venda_modalidade' in data:
        resumo.append(f'Venda por="{(data.get("venda_modalidade") or "Nenhum")}"')
    if 'valor' in data:
        resumo.append(f'Valor="{data.get("valor") or ""}"')
    if 'horas' in data:
        resumo.append(f'Horas="{data.get("horas") or ""}"')
    if 'area' in data:
        resumo.append(f'Área="{data.get("area") or "Nenhuma"}"')

    db.session.commit()
    log_action(session['user_id'], session['username'], 'editar_em_lote', 'course', None,
               f'{len(cursos_sel)} curso(s) -> ' + '; '.join(resumo))
    return jsonify({'ok': True, 'total': len(cursos_sel)})

@app.route('/cursos/exportar-excel')
@perm_check('can_view_cursos')
def cursos_exportar_excel():
    import openpyxl, re
    from openpyxl.styles import Font, PatternFill, Alignment, Border, Side
    from openpyxl.utils import get_column_letter
    tipo      = request.args.get('tipo','')
    area      = request.args.get('area','')
    status    = request.args.get('status','')
    busca     = request.args.get('q','')
    insersor  = request.args.get('insersor','')
    horas_min = request.args.get('horas_min','')
    horas_max = request.args.get('horas_max','')
    lista = _build_cursos_query(tipo, area, status, busca, insersor, horas_min, horas_max)

    TIPO_LABELS = {
        'pos':'Pós-Graduação','profissionalizante':'Profissionalizante','rapido':'Rápido',
        'pacote':'Pacote','terceiros':'Terceiros','evento':'Evento',
        'pratica_conectada':'Prática Conectada','pratica_estagio':'Prática Estágio',
        'projeto_ambiental':'Proj. Ambiental','ggbr':'GGBR','integra_edu':'Integra Edu',
    }

    wb = openpyxl.Workbook()
    ws = wb.active
    ws.title = 'Cursos'

    thin  = Side(style='thin', color='CBD5E1')
    bdr   = Border(left=thin, right=thin, top=thin, bottom=thin)
    wrap  = Alignment(wrap_text=True, vertical='top')
    center = Alignment(horizontal='center', vertical='center')
    hfill = PatternFill('solid', fgColor='6366F1')
    hfont = Font(bold=True, color='FFFFFF', size=10)

    STATUS_COLORS = {
        'ativo':'DCFCE7','em_edicao':'FEF9C3','descontinuado':'F1F5F9',
        'oculto':'EDE9FE','finalizado':'DBEAFE','externo':'FFEDD5',
    }

    headers = ['Nome do Curso','Tipo','Área','Status','CH','Duração','Valor (R$)',
               'Insersor','Cupom','Ano','Dono/Professor','Link Venda','Obs']
    for col, h in enumerate(headers, 1):
        c = ws.cell(row=1, column=col, value=h)
        c.fill = hfill; c.font = hfont; c.alignment = center; c.border = bdr
    ws.row_dimensions[1].height = 28

    for i, curso in enumerate(lista, 2):
        sc = STATUS_COLORS.get(curso.status, 'FFFFFF')
        row_fill = PatternFill('solid', fgColor=sc)
        vals = [
            curso.nome,
            TIPO_LABELS.get(curso.tipo, curso.tipo),
            curso.area or '',
            curso.status_label,
            curso.horas or '',
            curso.meses or '',
            curso.valor or '',
            curso.insersor or '',
            curso.cupom or '',
            curso.ano or '',
            curso.dono or '',
            curso.link_venda or '',
            curso.obs or '',
        ]
        for col, val in enumerate(vals, 1):
            cell = ws.cell(row=i, column=col, value=val)
            cell.border = bdr; cell.alignment = wrap; cell.fill = row_fill

    widths = [55,18,12,14,8,10,10,20,14,6,18,45,30]
    for i, w in enumerate(widths, 1):
        ws.column_dimensions[get_column_letter(i)].width = w
    ws.freeze_panes = 'A2'

    buf = io.BytesIO()
    wb.save(buf); buf.seek(0)
    from datetime import datetime as dt
    fname = f'cursos_inova_{dt.now().strftime("%Y%m%d_%H%M")}.xlsx'
    return send_file(buf, mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
                     as_attachment=True, download_name=fname)

@app.route('/cursos/relatorio')
@perm_check('can_view_cursos')
def cursos_relatorio():
    tipo      = request.args.get('tipo','')
    area      = request.args.get('area','')
    status    = request.args.get('status','')
    busca     = request.args.get('q','')
    insersor  = request.args.get('insersor','')
    horas_min = request.args.get('horas_min','')
    horas_max = request.args.get('horas_max','')
    lista = _build_cursos_query(tipo, area, status, busca, insersor, horas_min, horas_max)
    insersores = [u.username for u in User.query.order_by(User.username).all()]
    return render_template('cursos_relatorio.html', cursos=lista,
                           filtro_tipo=tipo, filtro_area=area, filtro_status=status,
                           filtro_insersor=insersor, busca=busca,
                           areas=AREAS_VALIDAS, insersores=insersores,
                           now=datetime.utcnow())

@app.route('/cursos/novo', methods=['GET','POST'])
@editor_required
@perm_check('can_view_cursos')
def curso_novo():
    if request.method == 'POST':
        d = request.form
        extra = {}
        # matrix fields passed as JSON string
        if d.get('disciplinas_json'):
            extra['disciplinas'] = json.loads(d['disciplinas_json'])
        imagens = [img for img in json.loads(d.get('imagens_json','[]') or '[]')
                   if img.get('url','').strip()]
        if imagens:
            extra['imagens'] = imagens
        c = Course(
            nome=d['nome'], tipo=d['tipo'], area=d.get('area',''),
            horas=d.get('horas',''), meses=d.get('meses',''), valor=d.get('valor',''),
            link_venda=d.get('link_venda',''), descricao=d.get('descricao',''),
            link_imagem=imagens[0]['url'] if imagens else '', insersor=','.join(d.getlist('insersores')) or session['username'],
            obs=d.get('obs',''), status=d.get('status','em_edicao'),
            ano=d.get('ano',''), cupom=d.get('cupom',''), dono=d.get('dono',''),
            venda_modalidade=d.get('venda_modalidade','') or None,
            data_finalizacao=_parse_data_form(d.get('data_finalizacao','')),
            link_video=d.get('link_video',''), limite_parcelas=d.get('limite_parcelas',''),
            extra_data=json.dumps(extra, ensure_ascii=False),
            created_by=session['user_id']
        )
        db.session.add(c)
        db.session.flush()
        # Save disciplines separately
        discs = json.loads(d.get('disciplinas_json','[]') or '[]')
        for i, disc in enumerate(discs):
            dd = Discipline(course_id=c.id, modulo=disc.get('modulo',''),
                           ordem=i+1, nome=disc.get('nome',''),
                           carga=disc.get('carga',''), professor=disc.get('professor',''),
                           cod_moodle=disc.get('cod_moodle',''), titulacao=disc.get('titulacao',''))
            db.session.add(dd)
        db.session.commit()
        log_action(session['user_id'], session['username'], 'criar', 'course', c.id, c.nome)
        flash('Curso criado com sucesso!', 'success')
        return redirect(url_for('curso_detalhe', id=c.id))
    usuarios = User.query.order_by(User.username).all()
    video_presets = VideoPreset.query.order_by(VideoPreset.ordem).all()
    venda_opcoes = VendaModalidadeOpcao.query.order_by(VendaModalidadeOpcao.ordem).all()
    return render_template('curso_form.html', curso=None, tipos=TIPOS_CURSO, areas=AREAS_VALIDAS,
                           usuarios=usuarios, video_presets=video_presets, venda_opcoes=venda_opcoes)

@app.route('/cursos/<int:id>')
@perm_check('can_view_cursos')
def curso_detalhe(id):
    c    = Course.query.get_or_404(id)
    disc = Discipline.query.filter_by(course_id=id).order_by(Discipline.ordem).all()
    logs = AuditLog.query.filter_by(entity='course', entity_id=id)\
                         .order_by(AuditLog.timestamp.desc()).all()
    extra = json.loads(c.extra_data) if c.extra_data else {}
    cupom_obj = Coupon.query.filter_by(nome=c.cupom).first() if c.cupom else None
    return render_template('curso_detalhe.html', c=c, disc=disc, logs=logs, extra=extra, cupom_obj=cupom_obj)

CAMPOS_CURSO_LABEL = {
    'nome': 'Nome', 'tipo': 'Tipo', 'area': 'Área', 'horas': 'Carga Horária',
    'meses': 'Duração', 'valor': 'Valor', 'link_venda': 'Link de Venda',
    'descricao': 'Descrição da Página de Venda', 'obs': 'Observações',
    'status': 'Status', 'cupom': 'Cupom', 'dono': 'Dono/Professor',
    'ano': 'Ano', 'insersor': 'Insersor',
    'venda_modalidade': 'Venda por', 'data_finalizacao': 'Data de Finalização',
    'link_video': 'Link do Vídeo', 'limite_parcelas': 'Limite de Parcelas',
}

@app.route('/cursos/<int:id>/editar', methods=['GET','POST'])
@editor_required
@perm_check('can_view_cursos')
def curso_editar(id):
    c = Course.query.get_or_404(id)
    if request.method == 'POST':
        antes = {campo: getattr(c, campo) for campo in CAMPOS_CURSO_LABEL}
        n_imagens_antes = len((json.loads(c.extra_data) if c.extra_data else {}).get('imagens', []))
        n_disc_antes = Discipline.query.filter_by(course_id=id).count()
        old_nome = c.nome
        d = request.form
        c.nome=d['nome']; c.tipo=d['tipo']; c.area=d.get('area','')
        c.horas=d.get('horas',''); c.meses=d.get('meses',''); c.valor=d.get('valor','')
        c.link_venda=d.get('link_venda',''); c.descricao=d.get('descricao','')
        c.obs=d.get('obs','')
        imagens = [img for img in json.loads(d.get('imagens_json','[]') or '[]')
                   if img.get('url','').strip()]
        extra_atual = json.loads(c.extra_data) if c.extra_data else {}
        if imagens: extra_atual['imagens'] = imagens
        else: extra_atual.pop('imagens', None)
        c.extra_data = json.dumps(extra_atual, ensure_ascii=False)
        c.link_imagem = imagens[0]['url'] if imagens else ''
        c.venda_modalidade = d.get('venda_modalidade','') or None
        c.data_finalizacao = _parse_data_form(d.get('data_finalizacao',''))
        c.link_video = d.get('link_video','')
        c.limite_parcelas = d.get('limite_parcelas','')
        novo_status = d.get('status', c.status)
        # Somente admin pode publicar (ativo); colaboradores podem marcar como finalizado no máximo
        if novo_status == 'ativo' and session.get('role') != 'admin':
            novo_status = c.status
        c.status = novo_status
        c.cupom=d.get('cupom','')
        c.dono=d.get('dono',''); c.ano=d.get('ano',''); c.updated_at=datetime.utcnow()
        ins_list = d.getlist('insersores')
        if ins_list: c.insersor = ','.join(ins_list)
        # Update disciplines — preserva plataforma_ok/plataforma_em por nome da disciplina
        if d.get('disciplinas_json') is not None:
            discs_novas = json.loads(d.get('disciplinas_json','[]') or '[]')
            # Mapa: nome normalizado → disciplina existente (para preservar status da plataforma)
            existentes = {ex.nome.strip().lower(): ex
                         for ex in Discipline.query.filter_by(course_id=id).all()}
            Discipline.query.filter_by(course_id=id).delete()
            for i, disc in enumerate(discs_novas):
                nome = disc.get('nome','')
                anterior = existentes.get(nome.strip().lower())
                dd = Discipline(
                    course_id=id,
                    modulo=disc.get('modulo',''),
                    ordem=i+1,
                    nome=nome,
                    carga=disc.get('carga',''),
                    professor=disc.get('professor',''),
                    cod_moodle=disc.get('cod_moodle',''),
                    titulacao=disc.get('titulacao',''),
                    plataforma_ok=anterior.plataforma_ok if anterior else False,
                    plataforma_em=anterior.plataforma_em if anterior else None
                )
                db.session.add(dd)
        db.session.commit()
        depois = {campo: getattr(c, campo) for campo in CAMPOS_CURSO_LABEL}
        detalhe = _resumo_mudancas(antes, depois, CAMPOS_CURSO_LABEL)
        n_disc_depois = Discipline.query.filter_by(course_id=id).count()
        extras = []
        if n_imagens_antes != len(imagens):
            extras.append(f'Imagens/Links de Capa: {n_imagens_antes} → {len(imagens)}')
        if n_disc_antes != n_disc_depois:
            extras.append(f'Disciplinas: {n_disc_antes} → {n_disc_depois}')
        if extras:
            detalhe = (detalhe + '; ' if detalhe else '') + '; '.join(extras)
        log_action(session['user_id'], session['username'], 'editar', 'course', id,
                   detalhe or 'Nenhum campo alterado')
        flash('Curso atualizado!', 'success')
        if d.get('from_page') == 'matrizes':
            return redirect(url_for('matrizes'))
        return redirect(url_for('curso_detalhe', id=id))
    disc = Discipline.query.filter_by(course_id=id).order_by(Discipline.ordem).all()
    disc_json = [{'modulo': d.modulo, 'ordem': d.ordem, 'nome': d.nome, 'carga': d.carga,
                  'professor': d.professor, 'titulacao': d.titulacao, 'cod_moodle': d.cod_moodle}
                 for d in disc]
    extra_atual = json.loads(c.extra_data) if c.extra_data else {}
    imagens_json = extra_atual.get('imagens') or ([{'url': c.link_imagem, 'descricao': ''}] if c.link_imagem else [])
    tipos = ['pos','profissionalizante','rapido','pacote','terceiros','evento','pratica_conectada','pratica_estagio','projeto_ambiental','ggbr','integra_edu']
    usuarios = User.query.order_by(User.username).all()
    video_presets = VideoPreset.query.order_by(VideoPreset.ordem).all()
    venda_opcoes = VendaModalidadeOpcao.query.order_by(VendaModalidadeOpcao.ordem).all()
    return render_template('curso_form.html', curso=c, disc=disc, disc_json=disc_json,
                           imagens_json=imagens_json, video_presets=video_presets, venda_opcoes=venda_opcoes,
                           tipos=TIPOS_CURSO, areas=AREAS_VALIDAS, usuarios=usuarios)

@app.route('/cursos/<int:id>/arquivar', methods=['POST'])
@editor_required
def curso_arquivar(id):
    c = Course.query.get_or_404(id)
    c.status = 'descontinuado'
    db.session.commit()
    log_action(session['user_id'], session['username'], 'arquivar', 'course', id, c.nome)
    flash('Curso arquivado (não excluído).', 'warning')
    return redirect(url_for('cursos'))

# Admins can hard-delete
@app.route('/cursos/<int:id>/excluir', methods=['POST'])
@admin_required
def curso_excluir(id):
    c = Course.query.get_or_404(id)
    nome = c.nome
    Discipline.query.filter_by(course_id=id).delete()
    db.session.delete(c)
    db.session.commit()
    log_action(session['user_id'], session['username'], 'excluir', 'course', id, nome)
    flash(f'Curso "{nome}" excluído permanentemente.', 'danger')
    return redirect(url_for('cursos'))

# ─── API SEARCH ────────────────────────────────────────────────────────────────

@app.route('/api/busca')
@login_required
def api_busca():
    q = request.args.get('q','')
    if len(q) < 2: return jsonify([])
    results = Course.query.filter(Course.nome.ilike(f'%{q}%')).limit(10).all()
    return jsonify([{'id': c.id, 'nome': c.nome, 'tipo': c.tipo, 'status': c.status,
                      'categoria': c.categoria or 'INOVA'} for c in results])

def _horas_num(valor):
    """Extrai o número inicial de um texto de carga horária livre (ex:
    '180', '40h', '30 horas') — usado só pra comparar cursos, nunca gravado."""
    if not valor:
        return None
    m = _re.match(r'^\s*(\d+\.?\d*)', str(valor))
    return float(m.group(1)) if m else None

@app.route('/api/curso/sugestao-matriz')
@editor_required
@perm_check('can_view_cursos')
def api_curso_sugestao_matriz():
    """Acha o curso existente mais parecido (mesmo tipo, de preferência
    mesma área, carga horária mais próxima) que já tenha matriz cadastrada,
    e devolve as disciplinas dele como rascunho — não grava nada, só serve
    de ponto de partida pra pessoa editar antes de salvar o curso novo."""
    tipo = request.args.get('tipo', '')
    area = request.args.get('area', '')
    horas = request.args.get('horas', '')
    excluir_id = request.args.get('excluir_id', type=int)
    if not tipo:
        return jsonify({'ok': False, 'erro': 'Escolha o tipo do curso primeiro.'})

    candidatos = Course.query.filter(Course.tipo == tipo).all()
    if excluir_id:
        candidatos = [c for c in candidatos if c.id != excluir_id]
    ids_candidatos = [c.id for c in candidatos]
    if not ids_candidatos:
        return jsonify({'ok': False, 'erro': 'Nenhum outro curso desse tipo foi encontrado.'})

    contagem = dict(
        db.session.query(Discipline.course_id, db.func.count(Discipline.id))
        .filter(Discipline.course_id.in_(ids_candidatos)).group_by(Discipline.course_id).all()
    )
    candidatos = [c for c in candidatos if contagem.get(c.id)]
    if not candidatos:
        return jsonify({'ok': False, 'erro': 'Nenhum curso desse tipo tem matriz cadastrada ainda pra servir de base.'})

    mesma_area = [c for c in candidatos if area and c.area == area]
    pool = mesma_area or candidatos

    alvo_horas = _horas_num(horas)
    if alvo_horas is not None:
        com_horas = [c for c in pool if _horas_num(c.horas) is not None]
        if com_horas:
            pool = sorted(com_horas, key=lambda c: abs(_horas_num(c.horas) - alvo_horas))
        else:
            pool = sorted(pool, key=lambda c: c.updated_at or c.created_at, reverse=True)
    else:
        pool = sorted(pool, key=lambda c: c.updated_at or c.created_at, reverse=True)

    similar = pool[0]
    discs = Discipline.query.filter_by(course_id=similar.id).order_by(Discipline.ordem).all()
    return jsonify({
        'ok': True,
        'curso_similar': {'nome': similar.nome, 'area': similar.area, 'horas': similar.horas},
        'disciplinas': [
            {'modulo': d.modulo or '', 'nome': d.nome or '', 'carga': d.carga or '',
             'professor': '', 'titulacao': ''}
            for d in discs
        ],
    })

# ─── ERP MOODLE (inserção de conteúdo — categoria separada do INOVA) ───────────
# Acompanhamento manual da equipe de inserção de materiais: cada linha é uma
# disciplina em inserção/concluída, com o curso digitado à mão (não depende
# do catálogo Course). Equipe interna (admin/editor) cria e edita; a equipe
# externa só enxerga quando ganha a permissão 'erp_moodle_acesso'.

@app.route('/erp-moodle')
@perm_check('can_view_erp_moodle')
def erp_moodle():
    f_status = request.args.get('status', '')
    f_insersor = request.args.get('insersor', '')
    f_busca = request.args.get('busca', '').strip()

    q = ErpMoodleItem.query
    if f_status in ('em_insercao', 'concluida'):
        q = q.filter_by(status=f_status)
    if f_insersor:
        q = q.filter(ErpMoodleItem.insersor_responsavel.ilike(f'%{f_insersor}%'))
    if f_busca:
        like = f'%{f_busca}%'
        q = q.filter(db.or_(ErpMoodleItem.nome_disciplina.ilike(like),
                             ErpMoodleItem.nome_curso.ilike(like)))
    itens = q.order_by(ErpMoodleItem.status.asc(), ErpMoodleItem.updated_at.desc()).all()

    total = ErpMoodleItem.query.count()
    total_em_insercao = ErpMoodleItem.query.filter_by(status='em_insercao').count()
    total_concluida = ErpMoodleItem.query.filter_by(status='concluida').count()

    insersores = sorted({i.insersor_responsavel for i in ErpMoodleItem.query.all() if i.insersor_responsavel})

    u = User.query.get(session['user_id'])
    return render_template('erp_moodle.html', itens=itens,
                           total=total, total_em_insercao=total_em_insercao, total_concluida=total_concluida,
                           f_status=f_status, f_insersor=f_insersor, f_busca=f_busca,
                           insersores=insersores, can_edit=u.can_edit_erp_moodle())

@app.route('/erp-moodle/novo', methods=['GET', 'POST'])
@editor_required
def erp_moodle_novo():
    if request.method == 'POST':
        d = request.form
        item = ErpMoodleItem(
            nome_disciplina=d.get('nome_disciplina', '').strip(),
            nome_curso=d.get('nome_curso', '').strip(),
            status=d.get('status', 'em_insercao'),
            data_conclusao=_parse_data_form(d.get('data_conclusao', '')),
            insersor_responsavel=d.get('insersor_responsavel', '').strip(),
            observacao=d.get('observacao', '').strip(),
            created_by=session['user_id'],
        )
        if item.status == 'concluida' and not item.data_conclusao:
            item.data_conclusao = date.today()
        db.session.add(item)
        db.session.commit()
        log_action(session['user_id'], session['username'], 'criar', 'erp_moodle', item.id, item.nome_disciplina)
        flash('Item adicionado ao ERP Moodle!', 'success')
        return redirect(url_for('erp_moodle'))
    return render_template('erp_moodle_form.html', item=None)

@app.route('/erp-moodle/<int:id>/editar', methods=['GET', 'POST'])
@editor_required
def erp_moodle_editar(id):
    item = ErpMoodleItem.query.get_or_404(id)
    if request.method == 'POST':
        d = request.form
        item.nome_disciplina = d.get('nome_disciplina', '').strip()
        item.nome_curso = d.get('nome_curso', '').strip()
        novo_status = d.get('status', 'em_insercao')
        if novo_status == 'concluida' and item.status != 'concluida':
            item.data_conclusao = _parse_data_form(d.get('data_conclusao', '')) or date.today()
        elif novo_status == 'em_insercao':
            item.data_conclusao = _parse_data_form(d.get('data_conclusao', ''))
        else:
            item.data_conclusao = _parse_data_form(d.get('data_conclusao', ''))
        item.status = novo_status
        item.insersor_responsavel = d.get('insersor_responsavel', '').strip()
        item.observacao = d.get('observacao', '').strip()
        db.session.commit()
        log_action(session['user_id'], session['username'], 'editar', 'erp_moodle', item.id, item.nome_disciplina)
        flash('Item atualizado!', 'success')
        return redirect(url_for('erp_moodle'))
    return render_template('erp_moodle_form.html', item=item)

@app.route('/erp-moodle/<int:id>/excluir', methods=['POST'])
@editor_required
def erp_moodle_excluir(id):
    item = ErpMoodleItem.query.get_or_404(id)
    nome = item.nome_disciplina
    db.session.delete(item)
    db.session.commit()
    log_action(session['user_id'], session['username'], 'excluir', 'erp_moodle', id, nome)
    flash('Item excluído.', 'success')
    return redirect(url_for('erp_moodle'))

@app.route('/api/curso/<int:id>/disciplinas')
@perm_check('can_view_erp_moodle')
def api_curso_disciplinas(id):
    """Lista as disciplinas da matriz de um curso, pra importar pro ERP
    Moodle sem digitar tudo de novo. Marca quais já têm item criado (mesmo
    curso + mesma disciplina) pra não duplicar sem querer."""
    curso = Course.query.get_or_404(id)
    discs = Discipline.query.filter_by(course_id=id).order_by(Discipline.ordem).all()
    ja_importadas = {
        i.nome_disciplina for i in ErpMoodleItem.query.filter_by(nome_curso=curso.nome).all()
    }
    return jsonify({
        'curso_id': curso.id, 'curso_nome': curso.nome,
        'disciplinas': [{'nome': d.nome, 'modulo': d.modulo or '',
                          'ja_importada': d.nome in ja_importadas} for d in discs],
    })

@app.route('/erp-moodle/importar', methods=['GET', 'POST'])
@editor_required
def erp_moodle_importar():
    if request.method == 'POST':
        curso_id = request.form.get('curso_id', '')
        curso_nome = request.form.get('curso_nome', '').strip()
        insersor = request.form.get('insersor_responsavel', '').strip()
        observacao = request.form.get('observacao', '').strip()
        nomes = request.form.getlist('disciplina_nome')
        status_list = request.form.getlist('disciplina_status')
        if not curso_nome or not nomes:
            flash('Selecione um curso e ao menos uma disciplina da matriz.', 'danger')
            return redirect(url_for('erp_moodle_importar', curso_id=curso_id))
        criados = 0
        for nome, status in zip(nomes, status_list):
            nome = nome.strip()
            if not nome:
                continue
            status = status if status in ('em_insercao', 'concluida') else 'em_insercao'
            item = ErpMoodleItem(
                nome_disciplina=nome, nome_curso=curso_nome, status=status,
                insersor_responsavel=insersor, observacao=observacao,
                created_by=session['user_id'],
            )
            if status == 'concluida':
                item.data_conclusao = date.today()
            db.session.add(item)
            criados += 1
        db.session.commit()
        log_action(session['user_id'], session['username'], 'importar', 'erp_moodle', None,
                   f'{criados} disciplina(s) da matriz de "{curso_nome}"')
        flash(f'{criados} disciplina(s) importada(s) da matriz de "{curso_nome}"!', 'success')
        return redirect(url_for('erp_moodle'))

    curso_id_inicial = request.args.get('curso_id', '')
    return render_template('erp_moodle_importar.html', curso_id_inicial=curso_id_inicial)

# ─── CUPONS ────────────────────────────────────────────────────────────────────

@app.route('/cupons')
@perm_check('can_view_cupons')
def cupons():
    busca = request.args.get('q', '')
    q = Coupon.query
    if busca:
        q = q.filter(Coupon.nome.ilike(f'%{busca}%'))
    cupons = q.order_by(Coupon.created_at.desc()).all()
    return render_template('cupons.html', cupons=cupons, busca=busca)

@app.route('/cupons/novo', methods=['GET','POST'])
@editor_required
def cupom_novo():
    if request.method == 'POST':
        d = request.form
        def parse_date(s):
            try: return datetime.strptime(s, '%Y-%m-%d').date()
            except: return None
        cp = Coupon(nome=d['nome'], quantidade=int(d.get('quantidade',0) or 0),
                    desconto=float(d.get('desconto',0) or 0),
                    cursos_tipo=d.get('cursos_tipo',''), limite_curso=int(d.get('limite_curso',1) or 1),
                    uso_unico=(d.get('uso_unico')=='SIM'),
                    data_inicial=parse_date(d.get('data_inicial','')),
                    data_final=parse_date(d.get('data_final','')),
                    obs=d.get('obs',''))
        db.session.add(cp)
        db.session.commit()
        log_action(session['user_id'], session['username'], 'criar', 'cupom', cp.id, cp.nome)
        flash('Cupom criado!', 'success')
        return redirect(url_for('cupons'))
    return render_template('cupom_form.html', cupom=None)

@app.route('/cupons/<int:id>/editar', methods=['GET','POST'])
@editor_required
def cupom_editar(id):
    cp = Coupon.query.get_or_404(id)
    if request.method == 'POST':
        d = request.form
        def parse_date(s):
            try: return datetime.strptime(s, '%Y-%m-%d').date()
            except: return None
        cp.nome=d['nome']; cp.quantidade=int(d.get('quantidade',0) or 0)
        cp.desconto=float(d.get('desconto',0) or 0)
        cp.cursos_tipo=d.get('cursos_tipo','')
        cp.limite_curso=int(d.get('limite_curso',1) or 1)
        cp.uso_unico=(d.get('uso_unico')=='SIM')
        cp.data_inicial=parse_date(d.get('data_inicial',''))
        cp.data_final=parse_date(d.get('data_final',''))
        cp.obs=d.get('obs','')
        db.session.commit()
        log_action(session['user_id'], session['username'], 'editar', 'cupom', id, cp.nome)
        flash('Cupom atualizado!', 'success')
        return redirect(url_for('cupons'))
    return render_template('cupom_form.html', cupom=cp)

# ─── REEMBOLSOS ────────────────────────────────────────────────────────────────

@app.route('/reembolsos')
@perm_check('can_view_reembolsos')
def reembolsos():
    busca      = request.args.get('q', '').strip()
    f_colab    = request.args.get('colab', '').strip()
    f_cat      = request.args.get('categoria', '').strip()
    f_pend     = request.args.get('pendencia', '').strip()

    q = Refund.query
    if busca:
        q = q.filter(db.or_(
            Refund.nome_aluno.ilike(f'%{busca}%'),
            Refund.nome_curso.ilike(f'%{busca}%')
        ))
    if f_colab:
        q = q.filter(Refund.colab.ilike(f'%{f_colab}%'))
    if f_cat:
        q = q.filter(Refund.categoria.ilike(f'%{f_cat}%'))

    items = q.order_by(Refund.created_at.desc()).all()

    # Filtro por pendência (feito em Python pois usa property)
    if f_pend:
        items = [r for r in items if r.pendencia[0] == f_pend]

    contagem = {'sem_solic1': 0, 'sem_solic2': 0, 'sem_aprovacao': 0, 'sem_exclusao': 0, 'concluido': 0}
    for r in Refund.query.all():
        contagem[r.pendencia[0]] += 1

    colabs = sorted({r.colab for r in Refund.query.all() if r.colab})
    cats   = sorted({r.categoria for r in Refund.query.all() if r.categoria})

    return render_template('reembolsos.html', items=items, contagem=contagem,
                           busca=busca, f_colab=f_colab, f_cat=f_cat, f_pend=f_pend,
                           colabs=colabs, cats=cats)

def _mask_meio(valor, manter_fim=4):
    """Mascara um dado sensível mantendo só os últimos caracteres visíveis
    (ex: CPF, PIX, celular) — pra planilha exportada não expor o dado
    completo mesmo pra quem tem permissão de baixar."""
    v = (valor or '').strip()
    if not v:
        return ''
    if len(v) <= manter_fim:
        return '*' * len(v)
    return '*' * (len(v) - manter_fim) + v[-manter_fim:]

def _mask_email(valor):
    v = (valor or '').strip()
    if not v or '@' not in v:
        return _mask_meio(v, manter_fim=2)
    usuario, _, dominio = v.partition('@')
    if len(usuario) <= 2:
        usuario_mask = '*' * len(usuario)
    else:
        usuario_mask = usuario[0] + '*' * (len(usuario) - 1)
    return f'{usuario_mask}@{dominio}'

@app.route('/reembolsos/exportar-excel')
@perm_check('can_manage_reembolsos')
def reembolsos_exportar_excel():
    """Dados de pagamento (CPF/celular/PIX/e-mail) saem mascarados mesmo
    pra quem tem permissão de ver a tela — a planilha baixada circula mais
    fácil (anexo, pendrive, nuvem pessoal) do que a tela do sistema."""
    import openpyxl
    from openpyxl.styles import Font, PatternFill, Alignment, Border, Side
    from openpyxl.utils import get_column_letter

    busca   = request.args.get('q', '').strip()
    f_colab = request.args.get('colab', '').strip()
    f_cat   = request.args.get('categoria', '').strip()
    f_pend  = request.args.get('pendencia', '').strip()

    q = Refund.query
    if busca:
        q = q.filter(db.or_(
            Refund.nome_aluno.ilike(f'%{busca}%'),
            Refund.nome_curso.ilike(f'%{busca}%')
        ))
    if f_colab:
        q = q.filter(Refund.colab.ilike(f'%{f_colab}%'))
    if f_cat:
        q = q.filter(Refund.categoria.ilike(f'%{f_cat}%'))
    items = q.order_by(Refund.created_at.desc()).all()
    if f_pend:
        items = [r for r in items if r.pendencia[0] == f_pend]

    wb = openpyxl.Workbook()
    ws = wb.active
    ws.title = 'Reembolsos'

    thin  = Side(style='thin', color='CBD5E1')
    bdr   = Border(left=thin, right=thin, top=thin, bottom=thin)
    wrap  = Alignment(wrap_text=True, vertical='top')
    center = Alignment(horizontal='center', vertical='center')
    hfill = PatternFill('solid', fgColor='6366F1')
    hfont = Font(bold=True, color='FFFFFF', size=10)

    headers = ['Colaborador', 'Aluno', 'Curso', 'Categoria', 'Data Compra', 'Data Solicitação',
               'Valor (R$)', 'Valor Estorno (R$)', '1ª Solicitação', '2ª Solicitação',
               'Data Aprovação', 'Curso Excluído', 'Situação', 'CPF', 'Celular', 'PIX',
               'E-mail Destino', 'Motivo', 'Obs']
    for col, h in enumerate(headers, 1):
        c = ws.cell(row=1, column=col, value=h)
        c.fill = hfill; c.font = hfont; c.alignment = center; c.border = bdr
    ws.row_dimensions[1].height = 28

    def fdata(d):
        return d.strftime('%d/%m/%Y') if d else ''

    for i, r in enumerate(items, 2):
        vals = [
            r.colab or '', r.nome_aluno or '', r.nome_curso or '', r.categoria or '',
            fdata(r.data_compra), fdata(r.data_solicitacao),
            r.valor or 0, r.valor_estorno or 0,
            fdata(r.solicitacao_1), fdata(r.solicitacao_2), fdata(r.data_aprovacao),
            fdata(r.curso_excluido), r.pendencia[1],
            _mask_meio(r.cpf, 3), _mask_meio(r.celular, 4), _mask_meio(r.pix, 4),
            _mask_email(r.email_destino),
            r.motivo or '', r.obs or '',
        ]
        for col, val in enumerate(vals, 1):
            cell = ws.cell(row=i, column=col, value=val)
            cell.border = bdr; cell.alignment = wrap
            if col in (7, 8):
                cell.number_format = '#,##0.00'

    larguras = [14, 24, 26, 16, 12, 14, 12, 14, 12, 12, 12, 12, 20, 16, 16, 20, 24, 24, 24]
    for col, w in enumerate(larguras, 1):
        ws.column_dimensions[get_column_letter(col)].width = w
    ws.freeze_panes = 'A2'

    buf = io.BytesIO()
    wb.save(buf)
    buf.seek(0)
    log_action(session['user_id'], session['username'], 'exportar_excel', 'reembolso', None,
               f'{len(items)} registro(s)')
    return send_file(buf, mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
                      as_attachment=True, download_name=f'reembolsos_{date.today().isoformat()}.xlsx')

@app.route('/reembolsos/novo', methods=['GET','POST'])
@editor_required
def reembolso_novo():
    if request.method == 'POST':
        r = _refund_from_form(request.form)
        db.session.add(r)
        db.session.commit()
        log_action(session['user_id'], session['username'], 'criar', 'reembolso', r.id, r.nome_aluno)
        flash('Reembolso registrado!', 'success')
        return redirect(url_for('reembolsos'))
    return render_template('reembolso_form.html', item=None)

@app.route('/reembolsos/<int:id>/editar', methods=['GET','POST'])
@editor_required
def reembolso_editar(id):
    r = Refund.query.get_or_404(id)
    if request.method == 'POST':
        d = request.form
        def pdate(s):
            try: return datetime.strptime(s, '%Y-%m-%d').date()
            except: return None
        r.colab          = d.get('colab','')
        r.nome_aluno     = d.get('nome_aluno','')
        r.nome_curso     = d.get('nome_curso','')
        r.categoria      = d.get('categoria','')
        r.data_compra    = pdate(d.get('data_compra',''))
        r.data_solicitacao = pdate(d.get('data_solicitacao',''))
        r.valor          = float(d.get('valor',0) or 0)
        r.valor_estorno  = float(d.get('valor_estorno',0) or 0)
        r.solicitacao_1  = pdate(d.get('solicitacao_1',''))
        r.solicitacao_2  = pdate(d.get('solicitacao_2',''))
        r.data_aprovacao = pdate(d.get('data_aprovacao',''))
        r.motivo           = d.get('motivo','')
        r.curso_excluido   = pdate(d.get('curso_excluido',''))
        r.obs              = d.get('obs','')
        r.concluido_manual = d.get('concluido_manual') == 'on'
        r.cpf              = d.get('cpf','')
        r.celular          = d.get('celular','')
        r.pix              = d.get('pix','')
        r.email_destino    = d.get('email_destino','')
        db.session.commit()
        log_action(session['user_id'], session['username'], 'editar', 'reembolso', id, r.nome_aluno)
        flash('Reembolso atualizado!', 'success')
        return redirect(url_for('reembolsos'))
    return render_template('reembolso_form.html', item=r)

@app.route('/reembolsos/<int:id>/enviar-email', methods=['POST'])
@login_required
def reembolso_enviar_email(id):
    r = Refund.query.get_or_404(id)
    if not r.email_destino:
        flash('Preencha o campo "E-mail de Destino" e salve antes de enviar.', 'danger')
        return redirect(url_for('reembolso_editar', id=id))
    valor_pago = ('R$ ' + f'{r.valor:.2f}'.replace('.', ',')) if r.valor else 'R$ —'
    valor_rec_num = r.valor_estorno or r.valor
    valor_rec = ('R$ ' + f'{valor_rec_num:.2f}'.replace('.', ',')) if valor_rec_num else 'R$ —'
    assunto = f'SOLICITAÇÃO DE REEMBOLSO INOVA CARREIRA - {r.nome_aluno}'
    corpo = (
        'Prezado(a)s,\n\n'
        'Por favor, solicito o pagamento de reembolso para o(a) seguinte aluno(a) matriculado(a) '
        f'no curso {r.nome_curso}, {r.motivo or ""}, encaminhado em anexo comprovantes de '
        'pagamento do aluno e do sistema da plataforma.\n\n'
        f'Valor Pago = {valor_pago}\n'
        f'Valor a receber: {valor_rec}\n\n'
        'Dados para pagamento:\n\n'
        f'Nome: {r.nome_aluno}\n'
        f'CPF : {r.cpf or "[CPF]"}\n'
        f'Celular: {r.celular or "[CELULAR]"}\n\n'
        f'PIX: {r.pix or "[PIX]"}\n\n\n'
        'Atenciosamente,\nINOVA Carreira'
    )
    if enviar_email(r.email_destino, assunto, corpo):
        log_action(session['user_id'], session['username'], 'enviar_email', 'reembolso', r.id, r.nome_aluno)
        flash(f'E-mail enviado para {r.email_destino}!', 'success')
    else:
        flash('Não foi possível enviar o e-mail agora. Tente novamente em instantes.', 'danger')
    return redirect(url_for('reembolso_editar', id=id))

@app.route('/reembolsos/<int:id>/excluir', methods=['POST'])
@admin_required
def reembolso_excluir(id):
    r = Refund.query.get_or_404(id)
    nome = r.nome_aluno
    db.session.delete(r)
    db.session.commit()
    log_action(session['user_id'], session['username'], 'excluir', 'reembolso', id, nome)
    flash(f'Reembolso de "{nome}" excluído.', 'success')
    return redirect(url_for('reembolsos'))

@app.route('/reembolsos/marcar-todos-concluidos', methods=['POST'])
@admin_required
def reembolsos_marcar_todos_concluidos():
    total = Refund.query.filter_by(concluido_manual=False).update({'concluido_manual': True})
    db.session.commit()
    log_action(session['user_id'], session['username'], 'marcar_todos', 'reembolso', None, f'{total} reembolsos')
    flash(f'{total} reembolso(s) marcado(s) como concluído.', 'success')
    return redirect(url_for('reembolsos'))

def _refund_from_form(d):
    def pdate(s):
        try: return datetime.strptime(s, '%Y-%m-%d').date()
        except: return None
    return Refund(
        colab=d.get('colab',''), nome_aluno=d.get('nome_aluno',''),
        nome_curso=d.get('nome_curso',''), categoria=d.get('categoria',''),
        data_compra=pdate(d.get('data_compra','')),
        data_solicitacao=pdate(d.get('data_solicitacao','')),
        valor=float(d.get('valor',0) or 0),
        valor_estorno=float(d.get('valor_estorno',0) or 0),
        solicitacao_1=pdate(d.get('solicitacao_1','')),
        solicitacao_2=pdate(d.get('solicitacao_2','')),
        data_aprovacao=pdate(d.get('data_aprovacao','')),
        motivo=d.get('motivo',''),
        curso_excluido=pdate(d.get('curso_excluido','')),
        obs=d.get('obs',''),
        concluido_manual=d.get('concluido_manual') == 'on',
        cpf=d.get('cpf',''),
        celular=d.get('celular',''),
        pix=d.get('pix',''),
        email_destino=d.get('email_destino',''),
    )

# ─── PAGAMENTOS DE TERCEIROS ───────────────────────────────────────────────────
# Controle de repasse de vendas para parceiros terceiros — só o admin acessa,
# insere ou apaga. Substitui a planilha usada antes para acompanhar o que já
# foi reportado/pago a cada parceiro.

def _pdate(s):
    try: return datetime.strptime(s, '%Y-%m-%d').date()
    except: return None

def _parse_valor_brl(s):
    """Aceita tanto '1076.90' quanto '1.076,90' ou '1076,90' — o campo é
    texto livre (não number) justamente para não perder os centavos quando
    o usuário digita com vírgula."""
    s = (s or '').strip().replace('R$', '').strip()
    if not s:
        return 0.0
    if ',' in s:
        s = s.replace('.', '').replace(',', '.')
    try:
        return round(float(s), 2)
    except ValueError:
        return 0.0

def _pagamentos_terceiros_filtrados():
    f_terceiro = request.args.get('terceiro', '').strip()
    f_curso    = request.args.get('curso', '', type=int)
    f_ano      = request.args.get('ano', '').strip()

    q = ThirdPartyPayment.query
    if f_terceiro:
        q = q.filter(ThirdPartyPayment.terceiro.ilike(f'%{f_terceiro}%'))
    if f_curso:
        q = q.filter(ThirdPartyPayment.course_id == f_curso)
    if f_ano:
        q = q.filter(ThirdPartyPayment.ano == f_ano)
    items = q.order_by(ThirdPartyPayment.data_emissao.desc()).all()
    return items, f_terceiro, f_curso, f_ano

@app.route('/pagamentos-terceiros')
@perm_check('can_view_pagamentos_terceiros')
def pagamentos_terceiros():
    items, f_terceiro, f_curso, f_ano = _pagamentos_terceiros_filtrados()

    # Terceiro -> Curso -> lista de registros (intervalos de pagamento)
    grupos = {}
    for p in items:
        nome_terceiro = p.terceiro or '(sem terceiro)'
        nome_curso = p.curso.nome if p.curso else '(curso não encontrado)'
        grupos.setdefault(nome_terceiro, {}).setdefault(nome_curso, []).append(p)

    grupos_ordenados = []
    subtotais_terceiro = {}
    for nome_terceiro in sorted(grupos.keys(), key=str.upper):
        cursos_do_terceiro = grupos[nome_terceiro]
        cursos_ordenados = []
        subtotal_terceiro = 0
        for nome_curso in sorted(cursos_do_terceiro.keys(), key=str.upper):
            registros = sorted(cursos_do_terceiro[nome_curso], key=lambda p: p.data_emissao or date.min, reverse=True)
            subtotal_curso = sum(p.valor or 0 for p in registros)
            subtotal_terceiro += subtotal_curso
            cursos_ordenados.append((nome_curso, registros, subtotal_curso))
        grupos_ordenados.append((nome_terceiro, cursos_ordenados))
        subtotais_terceiro[nome_terceiro] = subtotal_terceiro

    total_valor = sum(i.valor or 0 for i in items)
    terceiros = sorted({p.terceiro for p in ThirdPartyPayment.query.all() if p.terceiro})
    anos = sorted({p.ano for p in ThirdPartyPayment.query.all() if p.ano}, reverse=True)
    cursos_terceiros = Course.query.filter_by(tipo='terceiros').order_by(Course.nome).all()

    return render_template('pagamentos_terceiros.html', grupos=grupos_ordenados, subtotais_terceiro=subtotais_terceiro,
                           total_valor=total_valor, total_registros=len(items),
                           terceiros=terceiros, anos=anos, cursos_terceiros=cursos_terceiros,
                           f_terceiro=f_terceiro, f_curso=f_curso, f_ano=f_ano)

@app.route('/pagamentos-terceiros/exportar-excel')
@perm_check('can_manage_pagamentos_terceiros')
def pagamentos_terceiros_exportar_excel():
    import openpyxl
    from openpyxl.styles import Font, PatternFill, Alignment, Border, Side
    from openpyxl.utils import get_column_letter

    items, f_terceiro, f_curso, f_ano = _pagamentos_terceiros_filtrados()
    items = sorted(items, key=lambda p: (
        (p.terceiro or '').upper(),
        (p.curso.nome if p.curso else '').upper(),
        p.data_emissao or date.min,
    ))

    wb = openpyxl.Workbook()
    ws = wb.active
    ws.title = 'Pagamentos Terceiros'

    thin  = Side(style='thin', color='CBD5E1')
    bdr   = Border(left=thin, right=thin, top=thin, bottom=thin)
    wrap  = Alignment(wrap_text=True, vertical='top')
    center = Alignment(horizontal='center', vertical='center')
    hfill = PatternFill('solid', fgColor='6366F1')
    hfont = Font(bold=True, color='FFFFFF', size=10)

    headers = ['Terceiro', 'Curso', 'Data de Emissão', 'Início do Intervalo',
               'Fim do Intervalo', 'Ano', 'Valor (R$)', 'Observações']
    for col, h in enumerate(headers, 1):
        c = ws.cell(row=1, column=col, value=h)
        c.fill = hfill; c.font = hfont; c.alignment = center; c.border = bdr
    ws.row_dimensions[1].height = 28

    for i, p in enumerate(items, 2):
        vals = [
            p.terceiro or '',
            p.curso.nome if p.curso else '',
            p.data_emissao.strftime('%d/%m/%Y') if p.data_emissao else '',
            p.intervalo_inicio.strftime('%d/%m/%Y') if p.intervalo_inicio else '',
            p.intervalo_fim.strftime('%d/%m/%Y') if p.intervalo_fim else '',
            p.ano or '',
            p.valor or 0,
            p.obs or '',
        ]
        for col, val in enumerate(vals, 1):
            cell = ws.cell(row=i, column=col, value=val)
            cell.border = bdr; cell.alignment = wrap
            if col == 7:
                cell.number_format = '#,##0.00'

    widths = [22, 40, 16, 16, 16, 8, 14, 40]
    for i, w in enumerate(widths, 1):
        ws.column_dimensions[get_column_letter(i)].width = w
    ws.freeze_panes = 'A2'

    buf = io.BytesIO()
    wb.save(buf); buf.seek(0)
    fname = f'pagamentos_terceiros_{datetime.now().strftime("%Y%m%d_%H%M")}.xlsx'
    return send_file(buf, mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
                     as_attachment=True, download_name=fname)

@app.route('/pagamentos-terceiros/novo', methods=['GET', 'POST'])
@perm_check('can_manage_pagamentos_terceiros')
def pagamento_terceiro_novo():
    cursos_terceiros = Course.query.filter_by(tipo='terceiros').order_by(Course.nome).all()
    if request.method == 'POST':
        d = request.form
        p = ThirdPartyPayment(
            course_id=d.get('course_id', type=int),
            terceiro=d.get('terceiro', '').strip(),
            data_emissao=_pdate(d.get('data_emissao', '')),
            intervalo_inicio=_pdate(d.get('intervalo_inicio', '')),
            intervalo_fim=_pdate(d.get('intervalo_fim', '')),
            ano=d.get('ano', '').strip(),
            valor=_parse_valor_brl(d.get('valor', '')),
            obs=d.get('obs', ''),
            created_by=session['user_id'],
        )
        db.session.add(p)
        db.session.commit()
        log_action(session['user_id'], session['username'], 'criar', 'pagamento_terceiro', p.id, p.terceiro)
        flash('Pagamento de terceiro registrado!', 'success')
        return redirect(url_for('pagamentos_terceiros'))
    terceiro_prefill = request.args.get('terceiro', '').strip()
    return render_template('pagamento_terceiro_form.html', item=None, cursos_terceiros=cursos_terceiros,
                           terceiro_prefill=terceiro_prefill)

@app.route('/pagamentos-terceiros/<int:id>/editar', methods=['GET', 'POST'])
@perm_check('can_manage_pagamentos_terceiros')
def pagamento_terceiro_editar(id):
    p = ThirdPartyPayment.query.get_or_404(id)
    cursos_terceiros = Course.query.filter_by(tipo='terceiros').order_by(Course.nome).all()
    if request.method == 'POST':
        d = request.form
        p.course_id = d.get('course_id', type=int)
        p.terceiro = d.get('terceiro', '').strip()
        p.data_emissao = _pdate(d.get('data_emissao', ''))
        p.intervalo_inicio = _pdate(d.get('intervalo_inicio', ''))
        p.intervalo_fim = _pdate(d.get('intervalo_fim', ''))
        p.ano = d.get('ano', '').strip()
        p.valor = _parse_valor_brl(d.get('valor', ''))
        p.obs = d.get('obs', '')
        db.session.commit()
        log_action(session['user_id'], session['username'], 'editar', 'pagamento_terceiro', id, p.terceiro)
        flash('Pagamento de terceiro atualizado!', 'success')
        return redirect(url_for('pagamentos_terceiros'))
    return render_template('pagamento_terceiro_form.html', item=p, cursos_terceiros=cursos_terceiros)

@app.route('/pagamentos-terceiros/<int:id>/excluir', methods=['POST'])
@perm_check('can_manage_pagamentos_terceiros')
def pagamento_terceiro_excluir(id):
    p = ThirdPartyPayment.query.get_or_404(id)
    nome = p.terceiro
    db.session.delete(p)
    db.session.commit()
    log_action(session['user_id'], session['username'], 'excluir', 'pagamento_terceiro', id, nome)
    flash(f'Pagamento de "{nome}" excluído.', 'success')
    return redirect(url_for('pagamentos_terceiros'))

# ─── MATRIZES CURRICULARES ─────────────────────────────────────────────────────

@app.route('/disciplina/<int:disc_id>/toggle', methods=['POST'])
@login_required
def disciplina_toggle(disc_id):
    d = Discipline.query.get_or_404(disc_id)
    d.plataforma_ok = not d.plataforma_ok
    d.plataforma_em = datetime.utcnow() if d.plataforma_ok else None
    db.session.commit()
    if d.plataforma_ok:
        curso = Course.query.get(d.course_id)
        _notificar_disciplina_concluida(curso.nome if curso else '—', 1, d.nome)
    return jsonify({
        'ok': d.plataforma_ok, 'disc_id': disc_id,
        'data_formatada': d.plataforma_em.strftime('%d/%m/%Y') if d.plataforma_em else None,
    })

@app.route('/curso/<int:course_id>/disciplinas/marcar-todas', methods=['POST'])
@login_required
def disciplinas_marcar_todas(course_id):
    if session.get('role') != 'admin':
        return jsonify({'error': 'Acesso negado'}), 403
    marcar = request.json.get('marcar', True)
    discs = Discipline.query.filter_by(course_id=course_id).all()
    now = datetime.utcnow()
    for d in discs:
        d.plataforma_ok = marcar
        d.plataforma_em = now if marcar else None
    db.session.commit()
    if marcar and discs:
        curso = Course.query.get(course_id)
        _notificar_disciplina_concluida(curso.nome if curso else '—', len(discs))
    return jsonify({'ok': True, 'total': len(discs), 'marcar': marcar})

@app.route('/banco-disciplinas')
@perm_check('can_view_banco_disciplinas')
def banco_disciplinas():
    busca = request.args.get('q', '').strip()

    import unicodedata, re as _re
    def _norm(s):
        s = _re.sub(r'\s+', ' ', s.upper().strip())
        s = ''.join(c for c in unicodedata.normalize('NFKD', s) if not unicodedata.combining(c))
        return s

    todas = Discipline.query.order_by(Discipline.nome).all()
    cursos_map = {c.id: c for c in Course.query.all()}

    grupos = {}
    for d in todas:
        chave = _norm(d.nome)
        if busca and busca.lower() not in d.nome.lower():
            continue
        if chave not in grupos:
            grupos[chave] = {'nome': d.nome, 'cursos': [], 'ocorrencias': []}
        curso = cursos_map.get(d.course_id)
        if curso and curso.id not in [c.id for c in grupos[chave]['cursos']]:
            grupos[chave]['cursos'].append(curso)
        grupos[chave]['ocorrencias'].append(d)

    disciplinas_unicas = sorted(grupos.values(), key=lambda x: x['nome'])
    return render_template('banco_disciplinas.html',
                           disciplinas=disciplinas_unicas, busca=busca,
                           total_unicas=len(disciplinas_unicas),
                           total_ocorrencias=len(todas))


@app.route('/banco-disciplinas/exportar-excel')
@perm_check('can_view_banco_disciplinas')
def banco_disciplinas_exportar_excel():
    import openpyxl, re as _re, unicodedata
    from openpyxl.styles import Font, PatternFill, Alignment, Border, Side, GradientFill
    from openpyxl.utils import get_column_letter

    busca = request.args.get('q', '').strip()

    def _norm(s):
        s = _re.sub(r'\s+', ' ', s.upper().strip())
        return ''.join(c for c in unicodedata.normalize('NFKD', s) if not unicodedata.combining(c))

    TIPO_LABEL = {
        'pos': 'Pós-Graduação', 'profissionalizante': 'Profissionalizante',
        'rapido': 'Rápido', 'pacote': 'Pacote', 'terceiros': 'Terceiros',
        'evento': 'Evento', 'pratica_conectada': 'Prática Conectada',
        'pratica_estagio': 'Prática Estágio', 'projeto_ambiental': 'Proj. Ambiental',
        'ggbr': 'GGBR', 'integra_edu': 'Integra Edu',
    }

    todas = Discipline.query.order_by(Discipline.nome).all()
    cursos_map = {c.id: c for c in Course.query.all()}
    grupos = {}
    for d in todas:
        if busca and busca.lower() not in d.nome.lower():
            continue
        chave = _norm(d.nome)
        if chave not in grupos:
            grupos[chave] = {'nome': d.nome, 'ocorrencias': []}
        grupos[chave]['ocorrencias'].append((d, cursos_map.get(d.course_id)))

    wb = openpyxl.Workbook()

    # ── ABA 1: DISCIPLINAS × CURSOS (agrupado) ──────────────────────────────
    ws1 = wb.active
    ws1.title = 'Banco de Disciplinas'

    thin = Side(style='thin', color='E8E2DA')
    med  = Side(style='medium', color='F97316')
    bdr  = Border(left=thin, right=thin, top=thin, bottom=thin)
    bdr_disc = Border(left=med, right=thin, top=thin, bottom=thin)

    # Título
    ws1.merge_cells('A1:H1')
    title_cell = ws1['A1']
    title_cell.value = f'Gestor Acadêmico — Banco de Disciplinas'
    title_cell.font = Font(bold=True, size=14, color='F97316')
    title_cell.alignment = Alignment(horizontal='left', vertical='center')
    title_cell.fill = PatternFill('solid', fgColor='FFF7ED')
    ws1.row_dimensions[1].height = 30

    ws1.merge_cells('A2:H2')
    sub_cell = ws1['A2']
    sub_cell.value = f'Gerado em {datetime.now().strftime("%d/%m/%Y às %H:%M")} · {len(grupos)} disciplinas únicas · {len(todas)} ocorrências'
    sub_cell.font = Font(size=9, color='78716C', italic=True)
    sub_cell.alignment = Alignment(horizontal='left', vertical='center')
    ws1.row_dimensions[2].height = 18

    # Cabeçalho
    hfill  = PatternFill('solid', fgColor='F97316')
    hfont  = Font(bold=True, color='FFFFFF', size=10)
    center = Alignment(horizontal='center', vertical='center', wrap_text=True)
    wrap   = Alignment(wrap_text=True, vertical='top')
    left   = Alignment(horizontal='left', vertical='center', wrap_text=True)

    headers = ['Disciplina', 'CH', 'Módulo', 'Curso', 'Tipo', 'Área', 'Professor', 'Titulação']
    for col, h in enumerate(headers, 1):
        c = ws1.cell(row=3, column=col, value=h)
        c.fill = hfill; c.font = hfont; c.alignment = center; c.border = bdr
    ws1.row_dimensions[3].height = 24
    ws1.freeze_panes = 'A4'

    fill_disc  = PatternFill('solid', fgColor='FFF7ED')  # linha de disciplina (laranja suave)
    fill_curso = PatternFill('solid', fgColor='FFFFFF')   # linha de curso (branco)
    fill_alt   = PatternFill('solid', fgColor='FAFAF9')   # linha alternada

    row_idx = 4
    for idx, chave in enumerate(sorted(grupos.keys())):
        grupo = grupos[chave]
        ocors = grupo['ocorrencias']
        n_ocors = len(ocors)

        for i, (d, curso) in enumerate(ocors):
            is_first = (i == 0)
            tipo_label = TIPO_LABEL.get(curso.tipo, curso.tipo) if curso else ''
            fill = fill_disc if is_first else (fill_curso if i % 2 == 0 else fill_alt)

            vals = [
                grupo['nome'] if is_first else '',
                d.carga or '',
                d.modulo or '',
                curso.nome if curso else '',
                tipo_label,
                curso.area or '' if curso else '',
                d.professor or '',
                d.titulacao or '',
            ]
            for col, val in enumerate(vals, 1):
                cell = ws1.cell(row=row_idx, column=col, value=val)
                cell.border = bdr_disc if col == 1 else bdr
                cell.alignment = wrap
                cell.fill = fill
                if col == 1 and is_first:
                    cell.font = Font(bold=True, size=10)
            ws1.row_dimensions[row_idx].height = 16
            row_idx += 1

        # Linha separadora entre disciplinas
        if idx < len(grupos) - 1:
            for col in range(1, 9):
                cell = ws1.cell(row=row_idx, column=col, value='')
                cell.fill = PatternFill('solid', fgColor='F97316')
                cell.border = Border(top=Side(style='hair', color='F97316'))
            ws1.row_dimensions[row_idx].height = 3
            row_idx += 1

    for i, w in enumerate([44, 6, 16, 52, 18, 14, 24, 16], 1):
        ws1.column_dimensions[get_column_letter(i)].width = w

    # ── ABA 2: LISTA COMPLETA (uma linha por ocorrência) ────────────────────
    ws2 = wb.create_sheet('Lista Completa')

    ws2.merge_cells('A1:H1')
    t2 = ws2['A1']
    t2.value = 'Gestor Acadêmico — Lista Completa de Disciplinas'
    t2.font = Font(bold=True, size=13, color='F97316')
    t2.alignment = Alignment(horizontal='left', vertical='center')
    t2.fill = PatternFill('solid', fgColor='FFF7ED')
    ws2.row_dimensions[1].height = 28

    for col, h in enumerate(headers, 1):
        c = ws2.cell(row=2, column=col, value=h)
        c.fill = hfill; c.font = hfont; c.alignment = center; c.border = bdr
    ws2.row_dimensions[2].height = 22
    ws2.freeze_panes = 'A3'

    row2 = 3
    for chave in sorted(grupos.keys()):
        for d, curso in grupos[chave]['ocorrencias']:
            tipo_label = TIPO_LABEL.get(curso.tipo, curso.tipo) if curso else ''
            vals = [
                grupos[chave]['nome'], d.carga or '', d.modulo or '',
                curso.nome if curso else '',
                tipo_label,
                curso.area or '' if curso else '',
                d.professor or '', d.titulacao or '',
            ]
            fill_row = PatternFill('solid', fgColor='FFFFFF') if row2 % 2 == 1 else PatternFill('solid', fgColor='FAFAF9')
            for col, val in enumerate(vals, 1):
                cell = ws2.cell(row=row2, column=col, value=val)
                cell.border = bdr; cell.alignment = wrap; cell.fill = fill_row
            ws2.row_dimensions[row2].height = 15
            row2 += 1

    for i, w in enumerate([44, 6, 16, 52, 18, 14, 24, 16], 1):
        ws2.column_dimensions[get_column_letter(i)].width = w

    # ── ABA 3: RESUMO ESTATÍSTICO ────────────────────────────────────────────
    ws3 = wb.create_sheet('Resumo')
    ws3.merge_cells('A1:C1')
    t3 = ws3['A1']
    t3.value = 'Gestor Acadêmico — Resumo do Banco de Disciplinas'
    t3.font = Font(bold=True, size=13, color='F97316')
    t3.alignment = Alignment(horizontal='left', vertical='center')
    t3.fill = PatternFill('solid', fgColor='FFF7ED')
    ws3.row_dimensions[1].height = 28

    resumo_dados = [
        ('Total de disciplinas únicas', len(grupos)),
        ('Total de ocorrências', len(todas)),
        ('Média de cursos por disciplina', f'{len(todas)/len(grupos):.1f}' if grupos else '0'),
        ('', ''),
        ('Disciplinas com mais ocorrências', ''),
    ]
    row3 = 2
    for label, val in resumo_dados:
        ws3.cell(row=row3, column=1, value=label).font = Font(bold=True if not val else False, size=10)
        ws3.cell(row=row3, column=2, value=val).font = Font(bold=True, color='F97316', size=11)
        row3 += 1

    top_discs = sorted(grupos.values(), key=lambda x: len(x['ocorrencias']), reverse=True)[:10]
    for item in top_discs:
        ws3.cell(row=row3, column=1, value=item['nome']).font = Font(size=10)
        ws3.cell(row=row3, column=2, value=f"{len(item['ocorrencias'])} curso(s)").font = Font(color='F97316')
        row3 += 1

    ws3.column_dimensions['A'].width = 50
    ws3.column_dimensions['B'].width = 20

    buf = io.BytesIO()
    wb.save(buf); buf.seek(0)
    suffix = f'_{busca}' if busca else ''
    fname = f'banco_disciplinas{suffix}_{datetime.now().strftime("%Y%m%d_%H%M")}.xlsx'
    return send_file(buf, mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
                     as_attachment=True, download_name=fname)


@app.route('/banco-disciplinas/relatorio')
@perm_check('can_view_banco_disciplinas')
def banco_disciplinas_relatorio():
    busca = request.args.get('q', '').strip()

    import unicodedata, re as _re
    def _norm(s):
        s = _re.sub(r'\s+', ' ', s.upper().strip())
        return ''.join(c for c in unicodedata.normalize('NFKD', s) if not unicodedata.combining(c))

    TIPO_LABEL = {
        'pos': 'Pós-Graduação', 'profissionalizante': 'Profissionalizante',
        'rapido': 'Rápido', 'pacote': 'Pacote', 'terceiros': 'Terceiros',
        'evento': 'Evento', 'pratica_conectada': 'Prática Conectada',
        'pratica_estagio': 'Prática Estágio', 'projeto_ambiental': 'Proj. Ambiental',
        'ggbr': 'GGBR', 'integra_edu': 'Integra Edu',
    }

    todas = Discipline.query.order_by(Discipline.nome).all()
    cursos_map = {c.id: c for c in Course.query.all()}
    grupos = {}
    for d in todas:
        if busca and busca.lower() not in d.nome.lower():
            continue
        chave = _norm(d.nome)
        if chave not in grupos:
            grupos[chave] = {'nome': d.nome, 'cursos': [], 'ocorrencias': []}
        curso = cursos_map.get(d.course_id)
        if curso and curso.id not in [c.id for c in grupos[chave]['cursos']]:
            grupos[chave]['cursos'].append(curso)
        grupos[chave]['ocorrencias'].append((d, curso))

    disciplinas = sorted(grupos.values(), key=lambda x: x['nome'])
    total_ocors = len(todas)
    return render_template('banco_disciplinas_relatorio.html',
                           disciplinas=disciplinas, busca=busca,
                           total_unicas=len(disciplinas),
                           total_ocorrencias=total_ocors,
                           tipo_label=TIPO_LABEL,
                           gerado_em=datetime.now())


@app.route('/ia-assistente')
@perm_check('can_view_ia_assistente')
def ia_assistente():
    cursos_amostra = Course.query.filter(Course.status != 'descontinuado').order_by(Course.nome).limit(20).all()
    return render_template('ia_assistente.html', cursos_amostra=cursos_amostra)


@app.route('/api/ia/chat', methods=['POST'])
@login_required
def ia_chat():
    import unicodedata as _ud, re as _re

    data = request.json or {}
    pergunta = data.get('pergunta', '').strip()
    if not pergunta:
        return jsonify({'erro': 'Pergunta vazia'}), 400

    def _norm(s):
        s = _re.sub(r'\s+', ' ', s.upper().strip())
        return ''.join(c for c in _ud.normalize('NFKD', s) if not _ud.combining(c))

    def _contem(texto, *palavras):
        t = _norm(texto)
        return any(p in t for p in [_norm(w) for w in palavras])

    def _tipo_label(tipo):
        return {
            'pos': 'Pós-Graduação', 'profissionalizante': 'Profissionalizante',
            'rapido': 'Curso Rápido', 'pacote': 'Pacote', 'terceiros': 'Terceiros',
            'evento': 'Evento', 'pratica_conectada': 'Prática Conectada',
            'pratica_estagio': 'Prática Estágio', 'projeto_ambiental': 'Projeto Ambiental',
            'ggbr': 'GGBR', 'integra_edu': 'Integra Edu',
        }.get(tipo, tipo)

    p = pergunta
    linhas = []

    # ── CONHECIMENTO GERAL: ESTRUTURA DOS CURSOS NA PLATAFORMA ──────────
    # Baseado no POP 120-01 – Processo de Revisão e Curadoria de Materiais.
    # Diferente dos blocos abaixo (que consultam o banco do Gestor), este
    # responde com conhecimento fixo sobre como a Inova Carreira organiza
    # o conteúdo de cada modalidade — ex: "o que tem dentro de cada disciplina?"
    if _contem(p, 'dentro de cada disciplina', 'dentro do curso', 'dentro da disciplina',
               'o que tem no curso', 'conteudo do curso', 'conteúdo do curso',
               'como e estruturado', 'como é estruturado', 'como funciona a disciplina',
               'estrutura da disciplina', 'estrutura do curso', 'estrutura dos cursos',
               'materiais do curso', 'apostila', 'videoaula', 'atividade avaliativa',
               'quantas questoes', 'quantas questões', 'como e organizado o curso',
               'como é organizado o curso'):
        linhas = [
            "**Estrutura dos cursos na plataforma Inova Carreira:**\n",
            "📚 **Cursos Rápidos (Livres)** — geralmente 1 disciplina apenas:",
            "• Apostila em PDF",
            "• Videoaulas",
            "• Slides (quando disponíveis)",
            "• Áudios (quando disponíveis)",
            "• 1 atividade avaliativa no final, com 10 questões",
            "• Certificado após aprovação\n",
            "🎓 **Cursos Profissionalizantes** — geralmente 6 a 8 disciplinas:",
            "• Apostila, videoaulas, slides e áudios (quando disponíveis) por disciplina",
            "• Materiais complementares (quando houver)",
            "• 1 atividade avaliativa com 10 questões por disciplina",
            "• Certificado após concluir e ser aprovado em todas as disciplinas\n",
            "💻 **Em qualquer curso**, o aluno encontra: apresentação do curso, conteúdo "
            "organizado por tópicos/módulos, materiais de estudo (PDF, vídeos, slides e "
            "áudios, quando disponíveis), atividade avaliativa, resultado da avaliação e "
            "emissão de certificado (quando atende aos critérios de aprovação).\n",
            "_Pode haver pequenas diferenças conforme o tipo de curso ou como foi desenvolvido._",
        ]
        return jsonify({'ok': True, 'resposta': '\n'.join(linhas)})

    # ── CONHECIMENTO GERAL: VISÃO GERAL DA PLATAFORMA / MODALIDADES ─────
    if _contem(p, 'visao geral', 'visão geral', 'sobre a plataforma', 'o que e a inova',
               'o que é a inova', 'modalidades atendidas', 'quais modalidades',
               'como funciona a inova carreira', 'como funciona a plataforma'):
        linhas = [
            "**Plataforma Inova Carreira — visão geral** (baseado no POP 120-01):\n",
            "A plataforma contempla diferentes modalidades e demandas acadêmicas: Cursos "
            "Rápidos, Cursos Profissionalizantes, Pós-Graduação, Eventos, alunos internos "
            "da Unifatecie e alunos externos. Também atende Educação Corporativa, Práticas "
            "Conectadas, Projetos em Ambientes Profissionais e eventos institucionais.\n",
            "O suporte é feito pela Central de Atendimento da Inova Carreira, com "
            "intermédio da equipe de Inserção quando necessário.\n",
            "**Ferramentas usadas no processo:**",
            "• **Articulate** — criação e padronização dos conteúdos em HTML, com "
            "flexibilidade para alterações em tempo real.",
            "• **Planner** — controle diário de suporte, reembolsos e melhorias da "
            "plataforma.",
            "• **Trello** — monitoramento das demandas da Inserção, feedbacks e "
            "compartilhamento das disciplinas produzidas com a equipe de Produção de "
            "Materiais.\n",
            "🔗 Acesso à plataforma: https://www.inovacarreira.com.br/login",
        ]
        return jsonify({'ok': True, 'resposta': '\n'.join(linhas)})

    # ── CONHECIMENTO GERAL: FERRAMENTAS ESPECÍFICAS ─────────────────────
    if _contem(p, 'articulate'):
        return jsonify({'ok': True, 'resposta':
            "**Articulate** é a ferramenta utilizada para criação, edição e padronização "
            "dos conteúdos da plataforma Inova Carreira. Os materiais são feitos em "
            "documentos HTML, o que permite alterações e atualizações em tempo real, com "
            "mais flexibilidade e padronização visual."})
    if _contem(p, 'planner'):
        return jsonify({'ok': True, 'resposta':
            "**Planner** é usado diariamente para controlar as demandas relacionadas à "
            "plataforma Inova Carreira: acompanhamento de suporte, solicitações de "
            "reembolso, melhorias e correções de bugs da plataforma."})
    if _contem(p, 'trello'):
        return jsonify({'ok': True, 'resposta':
            "**Trello** é usado para monitorar as demandas da equipe de Inserção, "
            "gerenciar feedbacks, acompanhar a plataforma Inova Carreira e compartilhar "
            "as disciplinas produzidas com a equipe de Produção de Materiais."})
    if _contem(p, 'curadoria', 'link moodle'):
        return jsonify({'ok': True, 'resposta':
            "O **Sistema de Curadoria** é distinto da plataforma Inova Carreira. No "
            "processo de envio de disciplinas para lá, o formulário de cadastro tem um "
            "campo \"Link Moodle/Inova\", onde o colaborador insere o link da disciplina "
            "no Moodle. Esse campo faz parte do sistema de Curadoria e não é uma etapa "
            "da Inova Carreira."})

    # ── CONHECIMENTO GERAL: PROCESSO DE INSERÇÃO (ABAS DO CADASTRO) ─────
    if _contem(p, 'abas do curso', 'como cadastrar curso', 'como e inserido',
               'como é inserido', 'processo de insercao', 'processo de inserção',
               'modulos e disciplinas', 'módulos e disciplinas', 'como cadastrar disciplina'):
        linhas = [
            "**Como os cursos são estruturados na inserção (plataforma Inova Carreira):**\n",
            "🚀 **Curso Rápido** — 1 módulo com conteúdo e avaliação. Abas:",
            "• Dados do Curso — nome, categoria e descrição",
            "• Parâmetros — capa/vídeo, precificação, validades e canais de venda",
            "• Conteúdo do Curso — módulo, carga horária e aulas",
            "• Questões — banco de questões objetivas (mín. 1 alternativa certa e 1 "
            "errada), com prazo de certificação configurável\n",
            "🎓 **Curso Profissionalizante** — múltiplos módulos e disciplinas. Além das "
            "abas acima, tem:",
            "• Módulos — divisões do curso (equivalentes a capítulos)",
            "• Disciplinas — agrupamento de aulas dentro do módulo, cada uma pode ter um "
            "instrutor específico",
            "• Aulas — gerenciador de aulas por disciplina/módulo\n",
            "🎓 **Pós-Graduação** — segue a mesma estrutura do Profissionalizante, mas "
            "cada disciplina precisa indicar o professor responsável e sua titulação "
            "acadêmica.",
        ]
        return jsonify({'ok': True, 'resposta': '\n'.join(linhas)})

    # ── ESTATÍSTICAS GERAIS ─────────────────────────────
    if _contem(p, 'quantos', 'total', 'quantidade', 'estatistica', 'estatística', 'resumo', 'geral'):
        total = Course.query.count()
        ativos = Course.query.filter_by(status='ativo').count()
        em_ed = Course.query.filter_by(status='em_edicao').count()
        desc = Course.query.filter_by(status='descontinuado').count()
        n_disc = Discipline.query.count()
        import unicodedata as _ud2, re as _re2
        def _n2(s):
            s = _re2.sub(r'\s+', ' ', s.upper().strip())
            return ''.join(c for c in _ud2.normalize('NFKD', s) if not _ud2.combining(c))
        todas_d = Discipline.query.with_entities(Discipline.nome).all()
        unicas = len({_n2(d.nome) for d in todas_d})
        linhas = [
            f"Aqui está o resumo geral do sistema Gestor Acadêmico:\n",
            f"**Cursos cadastrados:** {total}",
            f"  • Ativos: {ativos}",
            f"  • Em edição: {em_ed}",
            f"  • Descontinuados: {desc}",
            f"\n**Banco de Disciplinas:** {unicas} disciplinas únicas ({n_disc} ocorrências no total)",
        ]
        por_tipo = db.session.query(Course.tipo, db.func.count(Course.id)).group_by(Course.tipo).order_by(db.func.count(Course.id).desc()).all()
        linhas.append("\n**Distribuição por tipo:**")
        for tipo, cnt in por_tipo:
            linhas.append(f"  • {_tipo_label(tipo)}: {cnt} curso(s)")
        return jsonify({'ok': True, 'resposta': '\n'.join(linhas)})

    # ── EVENTOS ─────────────────────────────────────────
    if _contem(p, 'evento', 'eventos', 'acontecendo', 'acontece', 'agenda', 'programacao', 'programação'):
        eventos = Course.query.filter_by(tipo='evento').order_by(Course.nome).all()
        if not eventos:
            return jsonify({'ok': True, 'resposta': 'Não há nenhum evento cadastrado no sistema no momento.'})
        linhas = [f"**Eventos cadastrados no sistema ({len(eventos)}):**\n"]
        for e in eventos:
            info = f"• **{e.nome}**"
            if e.area: info += f" — Área: {e.area}"
            if e.horas: info += f" | {e.horas}"
            if e.valor and e.valor not in ['-', '', 'None']: info += f" | R$ {e.valor}"
            if e.status: info += f" | Status: {e.status.replace('_', ' ').title()}"
            linhas.append(info)
        return jsonify({'ok': True, 'resposta': '\n'.join(linhas)})

    # ── PACOTES ─────────────────────────────────────────
    if _contem(p, 'pacote', 'pacotes', 'combo', 'bundle'):
        pacotes = Course.query.filter_by(tipo='pacote').order_by(Course.nome).all()
        if not pacotes:
            return jsonify({'ok': True, 'resposta': 'Não há pacotes cadastrados no sistema.'})
        linhas = [f"**Pacotes disponíveis ({len(pacotes)}):**\n"]
        for pac in pacotes:
            n_discs = Discipline.query.filter_by(course_id=pac.id).count()
            info = f"• **{pac.nome}**"
            if pac.valor and pac.valor not in ['-', '', 'None']: info += f" — R$ {pac.valor}"
            if n_discs: info += f" | {n_discs} disciplina(s)/curso(s)"
            if pac.status: info += f" | {pac.status.replace('_', ' ').title()}"
            linhas.append(info)
        return jsonify({'ok': True, 'resposta': '\n'.join(linhas)})

    # ── PÓS-GRADUAÇÃO ────────────────────────────────────
    if _contem(p, 'pos', 'pós', 'pos-graduacao', 'pós-graduação', 'graduacao', 'graduação', 'mba', 'especializacao', 'especialização'):
        cursos = Course.query.filter_by(tipo='pos').filter(Course.status != 'descontinuado').order_by(Course.nome).all()
        if not cursos:
            return jsonify({'ok': True, 'resposta': 'Não há cursos de pós-graduação ativos cadastrados.'})
        linhas = [f"**Cursos de Pós-Graduação ({len(cursos)}):**\n"]
        for c in cursos:
            info = f"• **{c.nome}**"
            if c.area: info += f" — {c.area}"
            if c.horas: info += f" | {c.horas}"
            linhas.append(info)
        return jsonify({'ok': True, 'resposta': '\n'.join(linhas)})

    # ── PROFISSIONALIZANTES ──────────────────────────────
    if _contem(p, 'profissionalizante', 'profissionalizantes', 'tecnico', 'técnico'):
        cursos = Course.query.filter_by(tipo='profissionalizante').filter(Course.status != 'descontinuado').order_by(Course.nome).all()
        if not cursos:
            return jsonify({'ok': True, 'resposta': 'Não há cursos profissionalizantes ativos.'})
        linhas = [f"**Cursos Profissionalizantes ({len(cursos)}):**\n"]
        for c in cursos:
            info = f"• **{c.nome}**"
            if c.area: info += f" — {c.area}"
            if c.horas: info += f" | {c.horas}"
            linhas.append(info)
        return jsonify({'ok': True, 'resposta': '\n'.join(linhas)})

    # ── CURSOS RÁPIDOS ───────────────────────────────────
    if _contem(p, 'rapido', 'rápido', 'rapidos', 'rápidos', 'curto', 'curta duracao', 'curta duração'):
        cursos = Course.query.filter_by(tipo='rapido').filter(Course.status != 'descontinuado').order_by(Course.nome).all()
        linhas = [f"**Cursos Rápidos ({len(cursos)}):**\n"]
        for c in cursos:
            info = f"• **{c.nome}**"
            if c.area: info += f" — {c.area}"
            if c.horas: info += f" | {c.horas}"
            linhas.append(info)
        return jsonify({'ok': True, 'resposta': '\n'.join(linhas) if linhas else 'Nenhum curso rápido cadastrado.'})

    # ── BUSCA POR ÁREA ───────────────────────────────────
    areas_map = {
        'saude': 'SAÚDE', 'saúde': 'SAÚDE',
        'negocios': 'NEGÓCIOS', 'negócios': 'NEGÓCIOS', 'negocio': 'NEGÓCIOS',
        'tecnologia': 'TECNOLOGIA', 'ti': 'TECNOLOGIA', 'informatica': 'TECNOLOGIA',
        'educacao': 'EDUCAÇÃO', 'educação': 'EDUCAÇÃO', 'pedagogia': 'EDUCAÇÃO',
        'criatividade': 'CRIATIVIDADE', 'design': 'CRIATIVIDADE', 'arte': 'CRIATIVIDADE',
        'gastronomia': 'GASTRONOMIA', 'culinaria': 'GASTRONOMIA', 'culinária': 'GASTRONOMIA',
    }
    area_encontrada = None
    p_norm = _norm(p)
    for chave, area_val in areas_map.items():
        if _norm(chave) in p_norm:
            area_encontrada = area_val
            break
    if area_encontrada:
        cursos = Course.query.filter_by(area=area_encontrada).filter(Course.status != 'descontinuado').order_by(Course.nome).all()
        if not cursos:
            return jsonify({'ok': True, 'resposta': f'Não encontrei cursos ativos na área de **{area_encontrada}**.'})
        linhas = [f"**Cursos na área de {area_encontrada} ({len(cursos)}):**\n"]
        for c in cursos:
            info = f"• **{c.nome}** ({_tipo_label(c.tipo)})"
            if c.horas: info += f" | {c.horas}"
            linhas.append(info)
        return jsonify({'ok': True, 'resposta': '\n'.join(linhas)})

    # ── DISCIPLINAS DO BANCO ─────────────────────────────
    if _contem(p, 'banco de disciplinas', 'disciplinas unicas', 'disciplinas únicas', 'todas as disciplinas', 'quais disciplinas temos', 'disciplinas disponiveis', 'disciplinas disponíveis'):
        todas = Discipline.query.with_entities(Discipline.nome).all()
        unicas = sorted({_norm(d.nome): d.nome for d in todas}.values())
        linhas = [f"**Banco de Disciplinas — {len(unicas)} disciplinas únicas cadastradas:**\n"]
        for i, nome in enumerate(unicas, 1):
            linhas.append(f"{i}. {nome}")
        return jsonify({'ok': True, 'resposta': '\n'.join(linhas)})

    # ── DISCIPLINAS PARA UM CURSO / SUGESTÃO ─────────────
    # Detecta padrões: "disciplinas para X", "disciplinas de X", "encaixam para X", "grade de X", "matriz de X"
    padroes_curso = [
        r'disciplinas?\s+(?:para|de|do|da)\s+(?:curso\s+(?:de\s+)?)?([\w\s]+)',
        r'encaixam?\s+(?:para|em|no|na)\s+(?:curso\s+(?:de\s+)?)?([\w\s]+)',
        r'grade\s+(?:curricular\s+)?(?:do|da|de)?\s+([\w\s]+)',
        r'matriz\s+(?:do|da|de)?\s+([\w\s]+)',
        r'sugest[aã]o\s+(?:para|de)?\s+(?:curso\s+(?:de\s+)?)?([\w\s]+)',
        r'sugira\s+(?:disciplinas?\s+)?(?:para|de)?\s+(?:curso\s+(?:de\s+)?)?([\w\s]+)',
    ]
    tema_busca = None
    for padrao in padroes_curso:
        m = _re.search(padrao, p, _re.IGNORECASE)
        if m:
            tema_busca = m.group(1).strip().rstrip('?.,! ')
            break

    # Também detecta perguntas sem padrão estruturado, ex: "o que tem no curso de administração"
    if not tema_busca:
        m = _re.search(r'curso\s+(?:de\s+|do\s+|da\s+)?([\w\s]{3,40}?)(?:\?|$|,|\.)', p, _re.IGNORECASE)
        if m:
            tema_busca = m.group(1).strip()

    if tema_busca:
        tema_norm = _norm(tema_busca)
        # 1. Busca curso exato ou similar no banco
        todos_cursos = Course.query.order_by(Course.nome).all()
        cursos_match = [c for c in todos_cursos if tema_norm in _norm(c.nome) or _norm(c.nome) in tema_norm]

        if cursos_match:
            # Encontrou curso(s) correspondente(s) — mostra as disciplinas
            linhas = []
            for c in cursos_match[:3]:
                discs = Discipline.query.filter_by(course_id=c.id).order_by(Discipline.ordem).all()
                linhas.append(f"**{c.nome}** ({_tipo_label(c.tipo)})")
                if c.area: linhas.append(f"Área: {c.area}")
                if discs:
                    linhas.append(f"Disciplinas da matriz ({len(discs)}):\n")
                    for d in discs:
                        item = f"• {d.nome}"
                        if d.carga: item += f" — {d.carga}"
                        if d.modulo: item += f" | Módulo: {d.modulo}"
                        linhas.append(item)
                else:
                    linhas.append("_(Este curso ainda não tem matriz cadastrada)_")
                linhas.append('')
            return jsonify({'ok': True, 'resposta': '\n'.join(linhas)})

        else:
            # Não achou curso — sugere disciplinas do banco que se relacionam ao tema
            todas_disc = Discipline.query.order_by(Discipline.nome).all()
            cursos_map = {c.id: c for c in todos_cursos}

            # Busca disciplinas cujo nome tenha palavras em comum com o tema
            palavras_tema = set(tema_norm.split())
            palavras_tema -= {'DE', 'DA', 'DO', 'EM', 'E', 'O', 'A', 'PARA', 'COM'}

            grupos = {}
            for d in todas_disc:
                chave = _norm(d.nome)
                if chave not in grupos:
                    grupos[chave] = {'nome': d.nome, 'cursos': [], 'relevancia': 0}
                # Calcula relevância por palavras em comum
                palavras_disc = set(_norm(d.nome).split())
                comuns = palavras_tema & palavras_disc
                grupos[chave]['relevancia'] = max(grupos[chave]['relevancia'], len(comuns))
                curso = cursos_map.get(d.course_id)
                if curso and curso.nome not in grupos[chave]['cursos']:
                    grupos[chave]['cursos'].append(curso.nome)

            relevantes = sorted(
                [v for v in grupos.values() if v['relevancia'] > 0],
                key=lambda x: -x['relevancia']
            )[:15]

            if relevantes:
                linhas = [
                    f"Não encontrei um curso com o nome **\"{tema_busca}\"** no sistema.",
                    f"Mas encontrei **{len(relevantes)} disciplinas** do nosso banco que podem se encaixar:\n"
                ]
                for item in relevantes:
                    linha = f"• **{item['nome']}**"
                    if item['cursos']:
                        linha += f" — presente em: {', '.join(item['cursos'][:2])}"
                        if len(item['cursos']) > 2: linha += f" +{len(item['cursos'])-2}"
                    linhas.append(linha)
                linhas.append(f"\n💡 Você pode ver o banco completo em **Banco de Disciplinas** no menu lateral.")
            else:
                # Busca mais ampla: qualquer disciplina, lista as mais usadas
                from sqlalchemy import func as sqlfunc
                top_discs = db.session.query(
                    Discipline.nome, sqlfunc.count(Discipline.id).label('cnt')
                ).group_by(Discipline.nome).order_by(sqlfunc.count(Discipline.id).desc()).limit(20).all()

                linhas = [
                    f"Não encontrei correspondências diretas para **\"{tema_busca}\"**.",
                    f"Aqui estão as disciplinas mais utilizadas nos nossos cursos que podem servir de base:\n"
                ]
                for nome, cnt in top_discs:
                    linhas.append(f"• {nome} ({cnt} curso(s))")
                linhas.append(f"\n💡 Acesse **Banco de Disciplinas** para ver todas as {len(grupos)} disciplinas únicas.")

            return jsonify({'ok': True, 'resposta': '\n'.join(linhas)})

    # ── BUSCA LIVRE POR NOME DE CURSO ────────────────────
    palavras = [w for w in _norm(p).split() if len(w) > 3 and w not in {'COMO', 'QUAL', 'QUAIS', 'ONDE', 'QUANDO', 'QUERO', 'TENHO', 'TEMOS', 'ESTA', 'ESTAO', 'SOBRE', 'MOSTRAR', 'LISTAR', 'LISTA', 'PODE', 'EXISTEM', 'EXISTE', 'CADASTRADO', 'SISTEMA'}]
    if palavras:
        resultados = []
        todos = Course.query.filter(Course.status != 'descontinuado').all()
        for c in todos:
            cnorm = _norm(c.nome)
            if any(w in cnorm for w in palavras):
                resultados.append(c)
        if resultados:
            linhas = [f"**Encontrei {len(resultados)} curso(s) relacionado(s):**\n"]
            for c in resultados[:15]:
                info = f"• **{c.nome}** ({_tipo_label(c.tipo)})"
                if c.area: info += f" — {c.area}"
                if c.horas: info += f" | {c.horas}"
                if c.status: info += f" | {c.status.replace('_',' ').title()}"
                linhas.append(info)
            if len(resultados) > 15:
                linhas.append(f"\n_...e mais {len(resultados)-15} curso(s). Refine a busca para ver todos._")
            return jsonify({'ok': True, 'resposta': '\n'.join(linhas)})

    # ── RESPOSTA PADRÃO ──────────────────────────────────
    total = Course.query.filter(Course.status != 'descontinuado').count()
    import unicodedata as _ud3, re as _re3
    def _n3(s):
        s = _re3.sub(r'\s+', ' ', s.upper().strip())
        return ''.join(c for c in _ud3.normalize('NFKD', s) if not _ud3.combining(c))
    unicas = len({_n3(d.nome) for d in Discipline.query.with_entities(Discipline.nome).all()})

    resposta = (
        f"Posso te ajudar a encontrar informações no sistema Gestor Acadêmico. "
        f"Temos **{total} cursos ativos** e **{unicas} disciplinas** no banco.\n\n"
        f"Experimente me perguntar:\n"
        f"• _\"Quais eventos estão cadastrados?\"_\n"
        f"• _\"Disciplinas para o curso de Administração\"_\n"
        f"• _\"Liste os cursos de pós-graduação\"_\n"
        f"• _\"Cursos na área de Saúde\"_\n"
        f"• _\"Quais pacotes temos?\"_\n"
        f"• _\"Resumo geral do sistema\"_"
    )
    return jsonify({'ok': True, 'resposta': resposta})


@app.route('/admin/marcar-tudo-concluido', methods=['POST'])
@admin_required
def admin_marcar_concluido():
    now = datetime.utcnow()
    total = Discipline.query.filter_by(plataforma_ok=False).update(
        {'plataforma_ok': True, 'plataforma_em': now}
    )
    db.session.commit()
    log_action(session['user_id'], session['username'], 'marcar_tudo', 'discipline', None,
               f'Marcou {total} disciplinas como concluídas')
    flash(f'{total} disciplina(s) marcada(s) como concluída(s)!', 'success')
    return redirect(request.referrer or url_for('matrizes'))


@app.route('/pacotes')
@perm_check('can_view_cursos')
def pacotes():
    busca = request.args.get('q', '').strip()

    todos = Course.query.filter_by(tipo='pacote').order_by(Course.nome).all()

    if busca:
        busca_low = busca.lower()
        disc_cids = {r[0] for r in db.session.query(Discipline.course_id)
                     .filter(Discipline.nome.ilike(f'%{busca}%')).all()}
        todos = [c for c in todos if busca_low in c.nome.lower() or c.id in disc_cids]

    pacote_data = []
    for c in todos:
        discs = Discipline.query.filter_by(course_id=c.id).order_by(Discipline.ordem).all()
        if busca and busca.lower() not in c.nome.lower():
            discs = [d for d in discs if busca.lower() in d.nome.lower()]
        pacote_data.append({'course': c, 'disciplines': discs})

    return render_template('pacotes.html', pacote_data=pacote_data, busca=busca)


@app.route('/admin/migrar-externos-para-pacotes', methods=['POST'])
@admin_required
def admin_migrar_externos():
    externos = Course.query.filter_by(status='externo').all()
    count = len(externos)
    for c in externos:
        c.tipo = 'pacote'
        c.status = 'ativo'
    db.session.commit()
    log_action(session['user_id'], session['username'], 'migrar', 'course', None,
               f'Migrou {count} curso(s) de status=externo para tipo=pacote')
    flash(f'{count} curso(s) migrado(s) de "Externo" para "Pacote" com sucesso!', 'success')
    return redirect(url_for('pacotes'))


@app.route('/matrizes')
@perm_check('can_view_matrizes')
def matrizes():
    busca = request.args.get('q', '').strip()
    # Sem "tipo" na URL nenhuma = primeira abertura (link da barra lateral) →
    # carrega só Profissionalizantes por padrão, pra não buscar tudo de uma
    # vez. O chip "Todos" manda tipo='' explicitamente pra pedir tudo mesmo.
    filtro_tipo_param = request.args.get('tipo')
    filtro_tipo = filtro_tipo_param if filtro_tipo_param is not None else 'profissionalizante'
    filtro_insersor = request.args.get('insersor', '').strip()
    filtro_pendente = request.args.get('pendente', '')

    import re

    # Conjunto completo (sem filtro de tipo/busca/insersor) — usado pros
    # chips de pendências por tipo e como base pra lista filtrada abaixo.
    # As disciplinas de todos eles são buscadas numa única query (evita
    # centenas de consultas, uma por curso). Inclui cursos sem nenhuma
    # disciplina ainda (ex: curso novo) pra eles aparecerem na Matriz
    # esperando a grade ser cadastrada, em vez de sumir da lista.
    # Só Pós/Profissionalizante/Pacote/GGBR — os demais tipos não têm
    # matriz curricular nesse formato.
    todos_para_chips = Course.query.filter(Course.tipo.in_(MATRIZES_TIPOS_PERMITIDOS))\
        .order_by(Course.tipo, Course.nome).all()

    discs_by_course = {}
    ids_todos = [c.id for c in todos_para_chips]
    if ids_todos:
        for d in (Discipline.query
                  .filter(Discipline.course_id.in_(ids_todos))
                  .order_by(Discipline.ordem).all()):
            discs_by_course.setdefault(d.course_id, []).append(d)

    def _parse_ch(val):
        if not val:
            return 0
        m = re.search(r'\d+', str(val))
        return int(m.group()) if m else 0

    # Filtra a lista exibida a partir do conjunto completo já carregado
    todos = todos_para_chips
    if filtro_tipo:
        todos = [c for c in todos if c.tipo == filtro_tipo]

    # Filtrar por busca (nome do curso OU nome da disciplina)
    if busca:
        busca_low = busca.lower()
        todos = [c for c in todos if busca_low in c.nome.lower() or
                 any(busca_low in d.nome.lower() for d in discs_by_course.get(c.id, []))]

    # Filtrar por insersor (campo pode ser comma-separated)
    if filtro_insersor:
        fi_low = filtro_insersor.lower()
        todos = [c for c in todos if c.insersor and
                 any(fi_low == p.strip().lower() for p in c.insersor.split(','))]

    course_data = []
    for c in todos:
        discs = discs_by_course.get(c.id, [])
        if busca and busca.lower() not in c.nome.lower():
            discs = [d for d in discs if busca.lower() in d.nome.lower()]
        total_ch = sum(_parse_ch(d.carga) for d in discs)
        ok_count = sum(1 for d in discs if d.plataforma_ok)
        course_data.append({'course': c, 'disciplines': discs, 'total_ch': total_ch, 'ok_count': ok_count})

    # Filtrar apenas pendentes (alguma disciplina não concluída)
    if filtro_pendente == '1':
        course_data = [item for item in course_data
                       if item['ok_count'] < len(item['disciplines'])]

    tipos_disponiveis = sorted({c.tipo for c in todos_para_chips})

    # Lista de insersores para o filtro (expandindo comma-separated)
    ins_set = set()
    for c in todos_para_chips:
        if c.insersor:
            for p in c.insersor.split(','):
                p = p.strip()
                if p:
                    ins_set.add(p)
    insersores_disponiveis = sorted(ins_set)

    total_pendentes = sum(1 for item in course_data
                          if item['ok_count'] < len(item['disciplines']))

    # Pendentes por tipo (todos os tipos, sem filtro atual)
    pendentes_por_tipo = {}
    for c in todos_para_chips:
        discs_c = discs_by_course.get(c.id, [])
        ok_c = sum(1 for d in discs_c if d.plataforma_ok)
        if ok_c < len(discs_c):
            pendentes_por_tipo[c.tipo] = pendentes_por_tipo.get(c.tipo, 0) + 1

    return render_template('matrizes.html', course_data=course_data, busca=busca,
                           filtro_tipo=filtro_tipo, tipos_disponiveis=tipos_disponiveis,
                           filtro_insersor=filtro_insersor, filtro_pendente=filtro_pendente,
                           insersores_disponiveis=insersores_disponiveis,
                           total_pendentes=total_pendentes,
                           pendentes_por_tipo=pendentes_por_tipo)

@app.route('/matrizes/marcar-tudo', methods=['POST'])
@perm_check('can_view_matrizes')
def matrizes_marcar_tudo():
    if session.get('role') != 'admin':
        return jsonify({'error': 'Acesso negado'}), 403
    data = request.json or {}
    marcar = data.get('marcar', True)
    filtro_tipo = data.get('tipo', '')
    filtro_status = data.get('status', '')
    filtro_insersor = data.get('insersor', '').strip()
    now = datetime.utcnow()
    q = Course.query.filter(Course.tipo.in_(MATRIZES_TIPOS_PERMITIDOS))
    if filtro_tipo:
        q = q.filter_by(tipo=filtro_tipo)
    if filtro_status:
        q = q.filter_by(status=filtro_status)
    cursos = q.all()
    if filtro_insersor:
        fi_low = filtro_insersor.lower()
        cursos = [c for c in cursos if c.insersor and
                  any(fi_low == p.strip().lower() for p in c.insersor.split(','))]
    course_ids = [c.id for c in cursos]
    discs = Discipline.query.filter(Discipline.course_id.in_(course_ids)).all()
    for d in discs:
        d.plataforma_ok = marcar
        d.plataforma_em = now if marcar else None
    db.session.commit()
    parts = []
    if filtro_tipo: parts.append(f'tipo={filtro_tipo}')
    if filtro_status: parts.append(f'status={filtro_status}')
    if filtro_insersor: parts.append(f'insersor={filtro_insersor}')
    filtro_desc = ' (' + ', '.join(parts) + ')' if parts else ' (todos)'
    log_action(session['user_id'], session['username'],
               'marcar_tudo' if marcar else 'desmarcar_tudo',
               'discipline', None,
               f'{"Marcou" if marcar else "Desmarcou"} {len(discs)} disciplinas{filtro_desc}')
    return jsonify({'ok': True, 'total': len(discs), 'marcar': marcar})

@app.route('/matrizes/relatorio')
@perm_check('can_view_matrizes')
def matrizes_relatorio():
    filtro_tipo = request.args.get('tipo', '')
    filtro_status = request.args.get('status', '')
    from sqlalchemy import exists as sql_exists
    import re
    q = Course.query.filter(sql_exists().where(Discipline.course_id == Course.id),
                            Course.tipo.in_(MATRIZES_TIPOS_PERMITIDOS))
    if filtro_tipo:
        q = q.filter_by(tipo=filtro_tipo)
    if filtro_status:
        q = q.filter_by(status=filtro_status)
    todos = q.order_by(Course.tipo, Course.nome).all()

    def _parse_ch(val):
        if not val: return 0
        m = re.search(r'\d+', str(val))
        return int(m.group()) if m else 0

    course_data = []
    for c in todos:
        discs = Discipline.query.filter_by(course_id=c.id).order_by(Discipline.ordem).all()
        total_ch = sum(_parse_ch(d.carga) for d in discs)
        course_data.append({'course': c, 'disciplines': discs, 'total_ch': total_ch})

    tipos_disponiveis = [r[0] for r in db.session.query(Course.tipo).join(
        Discipline, Discipline.course_id == Course.id)
        .filter(Course.tipo.in_(MATRIZES_TIPOS_PERMITIDOS)).distinct().all()]
    status_list = ['ativo', 'em_edicao', 'finalizado', 'descontinuado', 'oculto']

    return render_template('matrizes_relatorio.html', course_data=course_data,
                           filtro_tipo=filtro_tipo, filtro_status=filtro_status,
                           tipos_disponiveis=tipos_disponiveis, status_list=status_list,
                           now=datetime.utcnow())

@app.route('/matrizes/exportar-excel')
@perm_check('can_view_matrizes')
def matrizes_exportar_excel():
    import openpyxl, re
    from openpyxl.styles import Font, PatternFill, Alignment, Border, Side
    from openpyxl.utils import get_column_letter
    from sqlalchemy import exists as sql_exists

    filtro_tipo   = request.args.get('tipo', '')
    filtro_status = request.args.get('status', '')

    q = Course.query.filter(sql_exists().where(Discipline.course_id == Course.id),
                            Course.tipo.in_(MATRIZES_TIPOS_PERMITIDOS))
    if filtro_tipo:   q = q.filter_by(tipo=filtro_tipo)
    if filtro_status: q = q.filter_by(status=filtro_status)
    todos = q.order_by(Course.tipo, Course.nome).all()

    def _parse_ch(val):
        if not val: return 0
        m = re.search(r'\d+', str(val))
        return int(m.group()) if m else 0

    TIPO_LABELS = {
        'pos':'Pós-Graduação','profissionalizante':'Profissionalizante','rapido':'Rápido',
        'pacote':'Pacote','terceiros':'Terceiros','evento':'Evento',
        'pratica_conectada':'Prática Conectada','pratica_estagio':'Prática Estágio',
        'projeto_ambiental':'Proj. Ambiental','ggbr':'GGBR','integra_edu':'Integra Edu',
    }

    wb = openpyxl.Workbook()

    # ── Aba 1: Resumo por curso ─────────────────────────────────────────────
    ws_res = wb.active
    ws_res.title = 'Resumo'

    hdr_fill   = PatternFill('solid', fgColor='6366F1')
    hdr_font   = Font(bold=True, color='FFFFFF', size=10)
    ok_fill    = PatternFill('solid', fgColor='DCFCE7')
    pend_fill  = PatternFill('solid', fgColor='FEF9C3')
    thin       = Side(style='thin', color='CBD5E1')
    border     = Border(left=thin, right=thin, top=thin, bottom=thin)
    center     = Alignment(horizontal='center', vertical='center', wrap_text=True)
    wrap       = Alignment(wrap_text=True, vertical='top')

    res_headers = ['Curso', 'Tipo', 'Área', 'Status', 'CH Total', 'Duração',
                   'Valor (R$)', 'Insersor', 'Cupom', 'Ano', 'Link de Venda',
                   'Total Disc.', 'Na Plataforma', 'Pendentes', '% Concluído']
    for col, h in enumerate(res_headers, 1):
        c = ws_res.cell(row=1, column=col, value=h)
        c.fill = hdr_fill; c.font = hdr_font; c.alignment = center; c.border = border

    ws_res.row_dimensions[1].height = 30

    for row_idx, curso in enumerate(todos, 2):
        discs = Discipline.query.filter_by(course_id=curso.id).order_by(Discipline.ordem).all()
        total_ch  = sum(_parse_ch(d.carga) for d in discs)
        ok_count  = sum(1 for d in discs if d.plataforma_ok)
        pend      = len(discs) - ok_count
        pct       = round(ok_count / len(discs) * 100) if discs else 0
        values = [
            curso.nome,
            TIPO_LABELS.get(curso.tipo, curso.tipo),
            curso.area or '',
            curso.status_label,
            f'{total_ch}h' if total_ch else (curso.horas or ''),
            curso.meses or '',
            curso.valor or '',
            curso.insersor or '',
            curso.cupom or '',
            curso.ano or '',
            curso.link_venda or '',
            len(discs), ok_count, pend,
            f'{pct}%',
        ]
        row_fill = ok_fill if pct == 100 else (pend_fill if pct > 0 else None)
        for col, val in enumerate(values, 1):
            cell = ws_res.cell(row=row_idx, column=col, value=val)
            cell.border = border
            cell.alignment = wrap
            if row_fill and col <= 11:
                cell.fill = row_fill

    # Column widths resumo
    widths = [50, 18, 14, 14, 10, 10, 10, 20, 12, 8, 40, 10, 12, 10, 10]
    for i, w in enumerate(widths, 1):
        ws_res.column_dimensions[get_column_letter(i)].width = w

    # Freeze header
    ws_res.freeze_panes = 'A2'

    # ── Aba 2: Matrizes completas ────────────────────────────────────────────
    ws_mat = wb.create_sheet('Matrizes')

    mat_headers = ['Curso', 'Tipo', 'Área', 'Status', 'Insersor',
                   'Módulo', '#', 'Disciplina', 'CH', 'Professor', 'Titulação',
                   'Plataforma', 'Data Inserção']
    for col, h in enumerate(mat_headers, 1):
        c = ws_mat.cell(row=1, column=col, value=h)
        c.fill = hdr_fill; c.font = hdr_font; c.alignment = center; c.border = border
    ws_mat.row_dimensions[1].height = 28

    row_idx = 2
    for curso in todos:
        discs = Discipline.query.filter_by(course_id=curso.id).order_by(Discipline.ordem).all()
        for d in discs:
            values = [
                curso.nome,
                TIPO_LABELS.get(curso.tipo, curso.tipo),
                curso.area or '',
                curso.status_label,
                curso.insersor or '',
                d.modulo or '',
                d.ordem,
                d.nome,
                d.carga or '',
                d.professor or '',
                d.titulacao or '',
                'Sim' if d.plataforma_ok else 'Pendente',
                d.plataforma_em.strftime('%d/%m/%Y') if d.plataforma_ok and d.plataforma_em else '',
            ]
            row_fill = ok_fill if d.plataforma_ok else pend_fill
            for col, val in enumerate(values, 1):
                cell = ws_mat.cell(row=row_idx, column=col, value=val)
                cell.border = border
                cell.alignment = wrap
                cell.fill = row_fill
            row_idx += 1

    # Column widths matrizes
    mat_widths = [45, 18, 12, 14, 18, 12, 5, 45, 8, 22, 18, 10, 12]
    for i, w in enumerate(mat_widths, 1):
        ws_mat.column_dimensions[get_column_letter(i)].width = w
    ws_mat.freeze_panes = 'A2'

    # ── Salva e envia ────────────────────────────────────────────────────────
    buf = io.BytesIO()
    wb.save(buf)
    buf.seek(0)
    from datetime import datetime as dt
    ts = dt.now().strftime('%Y%m%d_%H%M')
    fname = f'matrizes_inova_{ts}.xlsx'
    return send_file(buf, mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
                     as_attachment=True, download_name=fname)

# ─── HISTÓRICO / AUDIT ─────────────────────────────────────────────────────────

@app.route('/historico')
@perm_check('can_view_historico')
def historico():
    page = request.args.get('page', 1, type=int)
    busca = request.args.get('q', '')
    acao = request.args.get('acao', '')
    entidade = request.args.get('entidade', '')
    q = AuditLog.query
    if busca:
        termo = f'%{busca}%'
        q = q.filter(db.or_(AuditLog.username.ilike(termo), AuditLog.detail.ilike(termo)))
    if acao:
        q = q.filter_by(action=acao)
    if entidade:
        q = q.filter_by(entity=entidade)
    logs = q.order_by(AuditLog.timestamp.desc()).paginate(page=page, per_page=50)
    acoes_disponiveis = [a[0] for a in db.session.query(AuditLog.action).distinct().order_by(AuditLog.action).all() if a[0]]
    entidades_disponiveis = [e[0] for e in db.session.query(AuditLog.entity).distinct().order_by(AuditLog.entity).all() if e[0]]
    return render_template('historico.html', logs=logs, busca=busca, filtro_acao=acao, filtro_entidade=entidade,
                           acoes_disponiveis=acoes_disponiveis, entidades_disponiveis=entidades_disponiveis)

# ─── USUÁRIOS ──────────────────────────────────────────────────────────────────

@app.route('/admin/visibilidade', methods=['GET', 'POST'])
@admin_required
def admin_visibilidade():
    """Padrão global do que fica visível pros usuários não-admin — módulos
    do menu lateral e widgets da dashboard. Não apaga nem sobrescreve
    permissão individual nenhuma: quem já tinha uma conta bloqueada em algo
    específico continua bloqueada, isso aqui só define o ponto de partida
    pra quem não tem bloqueio/liberação própria."""
    if request.method == 'POST':
        modulos = {m['id']: (request.form.get(f"modulo_{m['id']}") == 'on') for m in MODULOS_CATALOGO}
        widgets = {w['id']: (request.form.get(f"widget_{w['id']}") == 'on') for w in DASHBOARD_WIDGETS}
        for key, valor in [('modulos_visiveis', modulos), ('dashboard_widgets_visiveis', widgets)]:
            setting = AppSetting.query.get(key)
            if not setting:
                setting = AppSetting(key=key)
                db.session.add(setting)
            setting.value = json.dumps(valor)
        db.session.commit()
        log_action(session['user_id'], session['username'], 'editar', 'visibilidade', None,
                   'Atualizou o padrão de visibilidade de módulos/widgets')
        flash('Visibilidade padrão atualizada!', 'success')
        return redirect(url_for('admin_visibilidade'))

    return render_template('visibilidade.html',
        modulos_catalogo=MODULOS_CATALOGO, modulos_visiveis=_modulos_visiveis(),
        widgets_catalogo=DASHBOARD_WIDGETS, widgets_visiveis=_widgets_dashboard_visiveis())

@app.route('/usuarios')
@admin_required
def usuarios():
    busca = request.args.get('q', '')
    role_filtro = request.args.get('role', '')
    users = User.query.order_by(User.username).all()
    # todos os cursos, sem exceção de tipo ou status
    todos_cursos = Course.query.all()

    stats = {}
    for u in users:
        meus = [c for c in todos_cursos if c.insersor and _insersor_contains(c.insersor, u.username)]
        por_status = {}
        for c in meus:
            por_status[c.status] = por_status.get(c.status, 0) + 1
        por_tipo = {}
        for c in meus:
            por_tipo[c.tipo] = por_tipo.get(c.tipo, 0) + 1
        stats[u.id] = {
            'total':      len(meus),
            'ativos':     por_status.get('ativo', 0),
            'em_edicao':  por_status.get('em_edicao', 0),
            'finalizado': por_status.get('finalizado', 0),
            'desc':       por_status.get('descontinuado', 0),
            'oculto':     por_status.get('oculto', 0),
            'por_tipo':   por_tipo,
        }

    TIPO_LABEL = {
        'pos': 'Pós', 'profissionalizante': 'Profis.', 'rapido': 'Rápido',
        'pacote': 'Pacote', 'terceiros': 'Terceiros', 'evento': 'Evento',
        'pratica_conectada': 'Prática', 'pratica_estagio': 'Estágio',
        'projeto_ambiental': 'Proj. Amb.', 'ggbr': 'GGBR', 'integra_edu': 'Integra',
    }

    # Colaboradores que sumiram — sem login há DIAS_INATIVIDADE dias ou mais,
    # ou que nunca chegaram a logar (conta criada há tempo e nunca acessou).
    agora = datetime.utcnow()
    inativos = []
    for u in users:
        if u.role == 'admin':
            continue
        if u.ultimo_login:
            dias = (agora - u.ultimo_login).days
        else:
            dias = (agora - u.created_at).days if u.created_at else 0
        if dias >= DIAS_INATIVIDADE:
            inativos.append({'user': u, 'dias': dias, 'nunca_logou': u.ultimo_login is None})
    inativos.sort(key=lambda x: x['dias'], reverse=True)

    total_geral = len(users)
    users_filtrados = users
    if busca:
        termo = busca.lower()
        users_filtrados = [u for u in users_filtrados
                            if termo in u.username.lower() or termo in (u.nome or '').lower()]
    if role_filtro:
        users_filtrados = [u for u in users_filtrados if u.role == role_filtro]

    return render_template('usuarios.html', users=users_filtrados, stats=stats, tipo_label=TIPO_LABEL,
                           inativos=inativos, dias_inatividade=DIAS_INATIVIDADE,
                           busca=busca, filtro_role=role_filtro, total_geral=total_geral)


@app.route('/usuarios/<int:id>/cursos')
@admin_required
def usuario_cursos(id):
    u = User.query.get_or_404(id)
    todos_cursos = Course.query.filter(Course.insersor != None, Course.insersor != '')\
                               .order_by(Course.nome).all()
    meus = [c for c in todos_cursos if _insersor_contains(c.insersor, u.username)]

    disc_stats = {}
    for c in meus:
        total = Discipline.query.filter_by(course_id=c.id).count()
        pend  = Discipline.query.filter_by(course_id=c.id, plataforma_ok=False).count()
        disc_stats[c.id] = {'total': total, 'pend': pend, 'ok': total - pend}

    TIPO_LABEL = {
        'pos': 'Pós-Graduação', 'profissionalizante': 'Profissionalizante',
        'rapido': 'Rápido', 'pacote': 'Pacote', 'terceiros': 'Terceiros',
        'evento': 'Evento', 'pratica_conectada': 'Prática Conectada',
        'pratica_estagio': 'Prática Estágio', 'projeto_ambiental': 'Proj. Ambiental',
        'ggbr': 'GGBR', 'integra_edu': 'Integra Edu',
    }
    return render_template('usuario_cursos.html', u=u, cursos=meus,
                           disc_stats=disc_stats, tipo_label=TIPO_LABEL)

def _validar_email_institucional(email):
    email = (email or '').strip().lower()
    if not email or not email.endswith(EMAIL_DOMINIO_PERMITIDO):
        return None
    return email

@app.route('/usuarios/novo', methods=['GET','POST'])
@admin_required
def usuario_novo():
    if request.method == 'POST':
        d = request.form
        email = _validar_email_institucional(d.get('email'))
        if User.query.filter_by(username=d['username']).first():
            flash('Usuário já existe.', 'danger')
        elif not email:
            flash(f'O e-mail precisa ser institucional ({EMAIL_DOMINIO_PERMITIDO}).', 'danger')
        elif User.query.filter_by(email=email).first():
            flash('Já existe um usuário com esse e-mail.', 'danger')
        elif d.get('password') != d.get('confirmar_senha'):
            flash('As senhas não coincidem.', 'danger')
        else:
            perms = _perms_from_form(request.form)
            u = User(username=d['username'], nome=d.get('nome', '').strip(), email=email,
                     password=hash_pw(d['password']),
                     role=d['role'], permissoes=json.dumps(perms), must_change_password=True,
                     equipe=(d.get('equipe') == 'on'))
            db.session.add(u)
            db.session.commit()
            log_action(session['user_id'], session['username'], 'criar', 'user', u.id, u.username)
            flash('Usuário criado!', 'success')
            return redirect(url_for('usuarios'))
    return render_template('usuario_form.html', user=None)

@app.route('/usuarios/<int:id>/editar', methods=['GET','POST'])
@admin_required
def usuario_editar(id):
    u = User.query.get_or_404(id)
    if request.method == 'POST':
        d = request.form
        novo_username = d.get('username', '').strip()
        if novo_username and novo_username != u.username:
            existente = User.query.filter_by(username=novo_username).first()
            if existente:
                flash('Já existe um usuário com esse nome.', 'danger')
                return render_template('usuario_form.html', user=u)
            u.username = novo_username
        novo_email = _validar_email_institucional(d.get('email'))
        if not novo_email:
            flash(f'O e-mail precisa ser institucional ({EMAIL_DOMINIO_PERMITIDO}).', 'danger')
            return render_template('usuario_form.html', user=u)
        if novo_email != u.email and User.query.filter_by(email=novo_email).first():
            flash('Já existe um usuário com esse e-mail.', 'danger')
            return render_template('usuario_form.html', user=u)
        if d.get('password') and d.get('password') != d.get('confirmar_senha'):
            flash('As senhas não coincidem.', 'danger')
            return render_template('usuario_form.html', user=u)
        u.email = novo_email
        u.nome = d.get('nome', '').strip()
        u.role = d['role']
        u.permissoes = json.dumps(_perms_from_form(d))
        u.equipe = (d.get('equipe') == 'on')
        if d.get('password'):
            u.password = hash_pw(d['password'])
            u.must_change_password = True
        db.session.commit()
        log_action(session['user_id'], session['username'], 'editar', 'user', id, u.username)
        flash('Usuário atualizado!', 'success')
        return redirect(url_for('usuarios'))
    return render_template('usuario_form.html', user=u)

def _perms_from_form(d):
    keys = [
        'cursos_editar', 'cursos_excluir',
        'historico_ver', 'usuarios_gerenciar', 'backup_gerenciar',
        'erp_moodle_acesso',
        'block_historico', 'block_trocar_senha',
        'block_cursos', 'block_matrizes', 'block_banco_disciplinas',
        'block_ia_assistente', 'block_ferramentas',
        'block_mural', 'block_formularios', 'block_calendario',
        'somente_erp_moodle', 'conta_demo',
    ]
    return {k: (d.get(f'perm_{k}') == 'on') for k in keys}

@app.route('/usuarios/<int:id>/redefinir-senha', methods=['POST'])
@admin_required
def usuario_redefinir_senha(id):
    u = User.query.get_or_404(id)
    u.must_change_password = True
    db.session.commit()
    log_action(session['user_id'], session['username'], 'redefinir_senha', 'user', id, u.username)
    flash(f'"{u.username}" precisará trocar a senha no próximo login.', 'success')
    return redirect(url_for('usuarios'))

def _detectar_imagem(conteudo):
    """Detecta o tipo real da imagem pelos primeiros bytes (assinatura do
    arquivo) — nunca confia no mimetype que o navegador informou, porque
    é só um texto que o próprio upload manda e pode ser forjado. Devolve
    None se não reconhecer nenhum formato de imagem de verdade."""
    if conteudo[:3] == b'\xff\xd8\xff':
        return 'image/jpeg'
    if conteudo[:8] == b'\x89PNG\r\n\x1a\n':
        return 'image/png'
    if conteudo[:6] in (b'GIF87a', b'GIF89a'):
        return 'image/gif'
    if conteudo[:4] == b'RIFF' and conteudo[8:12] == b'WEBP':
        return 'image/webp'
    return None

@app.route('/usuarios/<int:id>/foto', methods=['POST'])
@admin_required
def usuario_foto_upload(id):
    u = User.query.get_or_404(id)
    arquivo = request.files.get('foto')
    if arquivo and arquivo.filename:
        conteudo = arquivo.read()
        if len(conteudo) > 3 * 1024 * 1024:
            flash('Foto muito grande (máx. 3MB).', 'danger')
        else:
            mimetype_real = _detectar_imagem(conteudo)
            if not mimetype_real:
                flash('Arquivo não parece ser uma imagem válida (jpg, png, gif ou webp).', 'danger')
            else:
                u.foto = conteudo
                u.foto_mimetype = mimetype_real
                db.session.commit()
                flash('Foto atualizada!', 'success')
    return redirect(url_for('usuario_editar', id=id))

@app.route('/usuarios/<int:id>/foto')
@login_required
def usuario_foto(id):
    u = User.query.get_or_404(id)
    if not u.foto:
        abort(404)
    return Response(u.foto, mimetype=u.foto_mimetype or 'image/jpeg')

@app.route('/usuarios/<int:id>/excluir', methods=['POST'])
@admin_required
def usuario_excluir(id):
    u = User.query.get_or_404(id)
    if u.id == session['user_id']:
        flash('Você não pode excluir sua própria conta.', 'danger')
        return redirect(url_for('usuarios'))
    username = u.username
    # Cursos e registros de histórico guardam o nome em texto separadamente
    # (Course.insersor, AuditLog.username), então desvincular o ID aqui não perde
    # o histórico — só evita a violação de chave estrangeira ao excluir o usuário.
    Course.query.filter_by(created_by=u.id).update({'created_by': None})
    AuditLog.query.filter_by(user_id=u.id).update({'user_id': None})
    db.session.delete(u)
    db.session.commit()
    log_action(session['user_id'], session['username'], 'excluir', 'user', id, username)
    flash(f'Usuário "{username}" excluído.', 'success')
    return redirect(url_for('usuarios'))

# ─── MURAL DA EQUIPE (mensagens + reação em emoji) ─────────────────────────────

EMOJIS_MURAL = ['👍', '❤️', '😂', '🎉', '👏', '🔥', '😮', '🙏']

def _mural_reacoes(mensagens, meu_id):
    reacoes_por_msg = {}
    minhas_reacoes = set()
    if mensagens:
        ids = [m.id for m in mensagens]
        rows = db.session.query(MuralReacao.mensagem_id, MuralReacao.emoji, db.func.count(MuralReacao.id))\
            .filter(MuralReacao.mensagem_id.in_(ids)).group_by(MuralReacao.mensagem_id, MuralReacao.emoji).all()
        for msg_id, emoji, qtd in rows:
            reacoes_por_msg.setdefault(msg_id, []).append({'emoji': emoji, 'qtd': qtd})
        minhas = MuralReacao.query.filter(MuralReacao.mensagem_id.in_(ids), MuralReacao.user_id == meu_id).all()
        minhas_reacoes = {(r.mensagem_id, r.emoji) for r in minhas}
    return reacoes_por_msg, minhas_reacoes

def _mural_minhas_conversas(meu_id):
    """Lista de pessoas com quem já troquei mensagem privada, mais recente
    primeiro."""
    enviei = db.session.query(MuralMensagem.mencionado_id, db.func.max(MuralMensagem.created_at))\
        .filter_by(privada=True, user_id=meu_id).group_by(MuralMensagem.mencionado_id)
    recebi = db.session.query(MuralMensagem.user_id, db.func.max(MuralMensagem.created_at))\
        .filter_by(privada=True, mencionado_id=meu_id).group_by(MuralMensagem.user_id)
    ultima_por_contato = {}
    for contato_id, quando in list(enviei.all()) + list(recebi.all()):
        if contato_id is None:
            continue
        if contato_id not in ultima_por_contato or quando > ultima_por_contato[contato_id]:
            ultima_por_contato[contato_id] = quando
    if not ultima_por_contato:
        return []
    usuarios = {u.id: u for u in User.query.filter(User.id.in_(ultima_por_contato.keys())).all()}
    return sorted(
        (usuarios[cid] for cid in ultima_por_contato if cid in usuarios),
        key=lambda c: ultima_por_contato[c.id], reverse=True
    )

@app.route('/mural')
@perm_check('can_view_mural')
def mural():
    u = User.query.get(session['user_id'])
    aba = request.args.get('aba', 'publico')
    contato = None
    if aba != 'publico':
        contato = User.query.get(aba) if aba.isdigit() else None
        if not contato or contato.id == u.id:
            aba = 'publico'
            contato = None

    if contato:
        mensagens = MuralMensagem.query.filter(
            MuralMensagem.privada == True,
            db.or_(
                db.and_(MuralMensagem.user_id == u.id, MuralMensagem.mencionado_id == contato.id),
                db.and_(MuralMensagem.user_id == contato.id, MuralMensagem.mencionado_id == u.id),
            )
        ).order_by(MuralMensagem.created_at.asc()).limit(300).all()
    else:
        mensagens = MuralMensagem.query.filter_by(privada=False).order_by(MuralMensagem.created_at.desc()).limit(80).all()

    reacoes_por_msg, minhas_reacoes = _mural_reacoes(mensagens, u.id)
    conversas = _mural_minhas_conversas(u.id)
    if contato and contato.id not in {c.id for c in conversas}:
        conversas = [contato] + conversas  # conversa nova, ainda sem mensagem enviada
    todos_usuarios = User.query.filter(User.id != u.id).order_by(User.username).all()

    return render_template('mural.html', mensagens=mensagens, emojis=EMOJIS_MURAL,
                           reacoes_por_msg=reacoes_por_msg, minhas_reacoes=minhas_reacoes,
                           aba=aba, contato=contato, conversas=conversas, todos_usuarios=todos_usuarios)

def _notificar_mencao_mural(mensagem):
    """Manda um e-mail pra quem recebeu a mensagem privada — só dispara nesse
    caso específico, recado público não gera e-mail pra ninguém (evita spam)."""
    if not mensagem.mencionado_id or mensagem.mencionado_id == mensagem.user_id:
        return
    alvo = User.query.get(mensagem.mencionado_id)
    if not alvo or not alvo.email:
        return
    autor_nome = mensagem.autor.username if mensagem.autor else 'Alguém'
    enviar_email(
        alvo.email,
        f'{autor_nome} te mandou uma mensagem privada no Mural da Equipe',
        f'{autor_nome} te mandou uma mensagem privada:\n\n'
        f'"{mensagem.texto[:500]}"\n\n'
        f'Acesse o sistema pra ver e responder: '
        f'{request.url_root.rstrip("/")}{url_for("mural", aba=mensagem.user_id)}'
    )

@app.route('/mural/nova', methods=['POST'])
@perm_check('can_view_mural')
def mural_nova():
    texto = request.form.get('texto', '').strip()
    resposta_a_id = request.form.get('resposta_a_id', type=int)
    mencionado_id = request.form.get('mencionado_id', type=int)
    if not texto:
        return redirect(url_for('mural'))
    privada = False
    if mencionado_id:
        alvo = User.query.get(mencionado_id)
        if not alvo or alvo.id == session['user_id']:
            flash('Destinatário inválido.', 'danger')
            return redirect(url_for('mural'))
        privada = True
        resposta_a_id = None  # conversa privada não usa "responder a" do mural público
    elif resposta_a_id and not MuralMensagem.query.get(resposta_a_id):
        resposta_a_id = None
    m = MuralMensagem(user_id=session['user_id'], texto=texto[:2000],
                      resposta_a_id=resposta_a_id, mencionado_id=mencionado_id, privada=privada)
    db.session.add(m)
    db.session.commit()
    if privada:
        try:
            _notificar_mencao_mural(m)
        except Exception as e:
            print(f'[ERRO E-MAIL MENSAGEM PRIVADA MURAL] {e}')
        return redirect(url_for('mural', aba=mencionado_id))
    return redirect(url_for('mural'))

@app.route('/mural/<int:id>/editar', methods=['POST'])
@perm_check('can_view_mural')
def mural_editar(id):
    m = MuralMensagem.query.get_or_404(id)
    if m.user_id != session['user_id']:
        return jsonify({'ok': False, 'erro': 'Você só pode editar suas próprias mensagens.'}), 403
    texto = (request.get_json(silent=True) or {}).get('texto', '').strip()
    if not texto:
        return jsonify({'ok': False, 'erro': 'Mensagem vazia.'}), 400
    m.texto = texto[:2000]
    m.editado_em = datetime.utcnow()
    db.session.commit()
    return jsonify({'ok': True, 'texto': m.texto})

@app.route('/mural/<int:id>/excluir', methods=['POST'])
@perm_check('can_view_mural')
def mural_excluir(id):
    m = MuralMensagem.query.get_or_404(id)
    u = User.query.get(session['user_id'])
    # Mensagem privada só o próprio autor apaga — nem admin mexe em conversa
    # alheia. Mensagem pública continua podendo ser removida pelo admin.
    pode_excluir = (m.user_id == u.id) or (u.role == 'admin' and not m.privada)
    aba_destino = (m.mencionado_id if m.user_id == u.id else m.user_id) if m.privada else 'publico'
    if not pode_excluir:
        flash('Você só pode excluir suas próprias mensagens.', 'danger')
        return redirect(url_for('mural', aba=aba_destino))
    MuralReacao.query.filter_by(mensagem_id=m.id).delete()
    MuralMensagem.query.filter_by(resposta_a_id=m.id).update({'resposta_a_id': None})
    db.session.delete(m)
    db.session.commit()
    flash('Mensagem excluída.', 'success')
    return redirect(url_for('mural', aba=aba_destino))

@app.route('/mural/<int:id>/reagir', methods=['POST'])
@perm_check('can_view_mural')
def mural_reagir(id):
    m = MuralMensagem.query.get_or_404(id)
    meu_id = session['user_id']
    if m.privada and meu_id not in (m.user_id, m.mencionado_id):
        return jsonify({'ok': False, 'erro': 'Você não faz parte dessa conversa.'}), 403
    data = request.get_json(silent=True) or {}
    emoji = (data.get('emoji') or '').strip()
    if not emoji or emoji not in EMOJIS_MURAL:
        return jsonify({'ok': False, 'erro': 'Emoji inválido.'}), 400
    existente = MuralReacao.query.filter_by(mensagem_id=id, user_id=session['user_id'], emoji=emoji).first()
    if existente:
        db.session.delete(existente)
        reagiu = False
    else:
        db.session.add(MuralReacao(mensagem_id=id, user_id=session['user_id'], emoji=emoji))
        reagiu = True
    db.session.commit()
    contagem = MuralReacao.query.filter_by(mensagem_id=id, emoji=emoji).count()
    return jsonify({'ok': True, 'reagiu': reagiu, 'contagem': contagem})

@app.route('/api/mural/novas-desde/<int:ultimo_id>')
@login_required
def api_mural_novas(ultimo_id):
    """Mensagens PÚBLICAS novas — usado tanto pro aviso 'atualizar' dentro da
    aba Mural quanto pro toast genérico (💬) em qualquer tela. Roda em
    polling de fundo, então quem não tem acesso ao Mural recebe uma
    resposta vazia (sem flash/redirect — isso é só pra navegação de página)."""
    u = User.query.get(session['user_id'])
    if not u or not u.can_view_mural():
        return jsonify({'novas': 0, 'ultimo_id': ultimo_id, 'mensagens': []})
    meu_id = session['user_id']
    novas = MuralMensagem.query.filter(MuralMensagem.id > ultimo_id, MuralMensagem.privada == False)\
        .order_by(MuralMensagem.id.asc()).limit(20).all()
    novas_de_outros = [m for m in novas if m.user_id != meu_id]
    return jsonify({
        'novas': len(novas_de_outros),
        'ultimo_id': novas[-1].id if novas else ultimo_id,
        'mensagens': [{'id': m.id, 'autor': m.autor.username if m.autor else '?', 'texto': m.texto[:140]}
                      for m in novas_de_outros],
    })

@app.route('/api/mural/privadas-desde/<int:ultimo_id>')
@login_required
def api_mural_privadas(ultimo_id):
    """Mensagens PRIVADAS novas endereçadas a mim — aviso separado (🔒),
    visualmente diferente do aviso de recado público, e que abre direto a
    conversa certa em vez do mural geral. Mesma degradação silenciosa de
    api_mural_novas pra quem não tem acesso ao Mural."""
    u = User.query.get(session['user_id'])
    if not u or not u.can_view_mural():
        return jsonify({'novas': 0, 'ultimo_id': ultimo_id, 'mensagens': []})
    meu_id = session['user_id']
    novas = MuralMensagem.query.filter(
        MuralMensagem.id > ultimo_id, MuralMensagem.privada == True, MuralMensagem.mencionado_id == meu_id
    ).order_by(MuralMensagem.id.asc()).limit(20).all()
    return jsonify({
        'novas': len(novas),
        'ultimo_id': novas[-1].id if novas else ultimo_id,
        'mensagens': [{'id': m.id, 'autor': m.autor.username if m.autor else '?',
                       'autor_id': m.user_id, 'texto': m.texto[:140]} for m in novas],
    })

# ─── FORMULÁRIOS ────────────────────────────────────────────────────────────────

def _formulario_pergunta_tem_resposta(pergunta_id):
    return db.session.query(FormularioRespostaItem.id).filter_by(pergunta_id=pergunta_id).first() is not None

def _salvar_perguntas_formulario(formulario, d):
    """Cria/atualiza as perguntas a partir do form de edição (campos
    perguntas[i][...]). Regra de ouro: editar a estrutura NUNCA pode
    corromper respostas já dadas.
    - Pergunta que já tem resposta não pode trocar de tipo (ignora o tipo
      enviado e mantém o original).
    - Opção de múltipla escolha que já foi escolhida por alguém nunca some
      da lista, mesmo que o admin a remova na tela — só dá pra adicionar
      opções novas.
    - Remover uma pergunta sem resposta apaga de vez; remover uma que já
      tem resposta apenas desativa (ativa=False), preservando o histórico."""
    total = int(d.get('perguntas_total') or 0)
    ordem = 0
    for i in range(total):
        prefixo = f'perguntas[{i}]'
        texto = (d.get(f'{prefixo}[texto]') or '').strip()
        if not texto:
            continue
        tipo = d.get(f'{prefixo}[tipo]') or 'texto'
        if tipo not in TIPOS_PERGUNTA_FORMULARIO:
            tipo = 'texto'
        obrigatoria = d.get(f'{prefixo}[obrigatoria]') == 'on'
        removida = d.get(f'{prefixo}[removida]') == '1'
        opcoes_novas = [o.strip() for o in (d.get(f'{prefixo}[opcoes]') or '').split('\n') if o.strip()]
        pergunta_id = d.get(f'{prefixo}[id]')

        if pergunta_id:
            p = FormularioPergunta.query.filter_by(id=int(pergunta_id), formulario_id=formulario.id).first()
            if not p:
                continue
            tem_resposta = _formulario_pergunta_tem_resposta(p.id)
            p.texto = texto
            p.obrigatoria = obrigatoria
            if not tem_resposta:
                p.tipo = tipo
            if p.tipo == 'multipla_escolha':
                usadas = {v for (v,) in db.session.query(FormularioRespostaItem.valor_texto)
                          .filter_by(pergunta_id=p.id).distinct().all() if v}
                for opcao_usada in usadas:
                    if opcao_usada not in opcoes_novas:
                        opcoes_novas.append(opcao_usada)
                p.opcoes = json.dumps(opcoes_novas, ensure_ascii=False)
            if removida:
                if tem_resposta:
                    p.ativa = False
                else:
                    db.session.delete(p)
                    continue
            else:
                p.ativa = True
            p.ordem = ordem
        else:
            if removida:
                continue
            p = FormularioPergunta(formulario_id=formulario.id, texto=texto, tipo=tipo,
                                    obrigatoria=obrigatoria, ordem=ordem, ativa=True)
            if tipo == 'multipla_escolha':
                p.opcoes = json.dumps(opcoes_novas, ensure_ascii=False)
            db.session.add(p)
        ordem += 1

@app.route('/formularios')
@perm_check('can_view_formularios')
def formularios():
    u = User.query.get(session['user_id'])
    if u.role == 'admin':
        forms = Formulario.query.order_by(Formulario.created_at.desc()).all()
    else:
        forms = Formulario.query.filter_by(ativo=True).order_by(Formulario.created_at.desc()).all()
    minhas_respostas = {r.formulario_id for r in FormularioResposta.query.filter_by(user_id=u.id).all()}
    participantes = dict(
        db.session.query(FormularioResposta.formulario_id, db.func.count(db.func.distinct(FormularioResposta.user_id)))
        .group_by(FormularioResposta.formulario_id).all()
    )
    return render_template('formularios.html', forms=forms, minhas_respostas=minhas_respostas,
                           participantes=participantes)

@app.route('/formularios/novo', methods=['GET', 'POST'])
@admin_required
def formulario_novo():
    if request.method == 'POST':
        d = request.form
        titulo = (d.get('titulo') or '').strip()
        if not titulo:
            flash('Dê um título ao formulário.', 'danger')
            return redirect(url_for('formulario_novo'))
        f = Formulario(titulo=titulo, descricao=(d.get('descricao') or '').strip(),
                       ativo=(d.get('ativo') == 'on'), unica_resposta=(d.get('unica_resposta') == 'on'),
                       created_by=session['user_id'])
        db.session.add(f)
        db.session.flush()
        _salvar_perguntas_formulario(f, d)
        db.session.commit()
        log_action(session['user_id'], session['username'], 'criar', 'formulario', f.id, f.titulo)
        flash('Formulário criado!', 'success')
        return redirect(url_for('formularios'))
    return render_template('formulario_form.html', formulario=None, perguntas=[], tem_resposta_ids=set())

@app.route('/formularios/<int:id>/editar', methods=['GET', 'POST'])
@admin_required
def formulario_editar(id):
    f = Formulario.query.get_or_404(id)
    if request.method == 'POST':
        d = request.form
        titulo = (d.get('titulo') or '').strip()
        if not titulo:
            flash('Dê um título ao formulário.', 'danger')
            return redirect(url_for('formulario_editar', id=id))
        f.titulo = titulo
        f.descricao = (d.get('descricao') or '').strip()
        f.ativo = (d.get('ativo') == 'on')
        f.unica_resposta = (d.get('unica_resposta') == 'on')
        _salvar_perguntas_formulario(f, d)
        db.session.commit()
        log_action(session['user_id'], session['username'], 'editar', 'formulario', f.id, f.titulo)
        flash('Formulário atualizado!', 'success')
        return redirect(url_for('formularios'))
    perguntas = FormularioPergunta.query.filter_by(formulario_id=f.id, ativa=True)\
        .order_by(FormularioPergunta.ordem).all()
    tem_resposta_ids = {p.id for p in perguntas if _formulario_pergunta_tem_resposta(p.id)}
    return render_template('formulario_form.html', formulario=f, perguntas=perguntas, tem_resposta_ids=tem_resposta_ids)

@app.route('/formularios/<int:id>/excluir', methods=['POST'])
@admin_required
def formulario_excluir(id):
    f = Formulario.query.get_or_404(id)
    if FormularioResposta.query.filter_by(formulario_id=f.id).first():
        flash('Este formulário já tem respostas registradas — não pode ser excluído. Desative-o em vez disso, pra preservar o histórico.', 'danger')
        return redirect(url_for('formularios'))
    FormularioPergunta.query.filter_by(formulario_id=f.id).delete()
    db.session.delete(f)
    db.session.commit()
    log_action(session['user_id'], session['username'], 'excluir', 'formulario', id, f.titulo)
    flash('Formulário excluído.', 'success')
    return redirect(url_for('formularios'))

@app.route('/formularios/<int:id>/responder', methods=['GET', 'POST'])
@perm_check('can_view_formularios')
def formulario_responder(id):
    f = Formulario.query.get_or_404(id)
    u = User.query.get(session['user_id'])
    if not f.ativo and u.role != 'admin':
        flash('Este formulário não está mais recebendo respostas.', 'warning')
        return redirect(url_for('formularios'))
    perguntas = FormularioPergunta.query.filter_by(formulario_id=f.id, ativa=True)\
        .order_by(FormularioPergunta.ordem).all()

    resposta_existente = None
    valores_existentes = {}
    if f.unica_resposta:
        resposta_existente = FormularioResposta.query.filter_by(formulario_id=f.id, user_id=u.id).first()
        if resposta_existente:
            valores_existentes = {i.pergunta_id: i for i in
                                  FormularioRespostaItem.query.filter_by(resposta_id=resposta_existente.id).all()}

    if request.method == 'POST':
        d = request.form
        for p in perguntas:
            valor = (d.get(f'pergunta_{p.id}') or '').strip()
            if p.obrigatoria and not valor:
                flash(f'A pergunta "{p.texto}" é obrigatória.', 'danger')
                return redirect(url_for('formulario_responder', id=id))

        if f.unica_resposta and resposta_existente:
            resposta = resposta_existente
            FormularioRespostaItem.query.filter_by(resposta_id=resposta.id).delete()
        else:
            resposta = FormularioResposta(formulario_id=f.id, user_id=u.id)
            db.session.add(resposta)
            db.session.flush()

        for p in perguntas:
            valor = (d.get(f'pergunta_{p.id}') or '').strip()
            if not valor:
                continue
            item = FormularioRespostaItem(resposta_id=resposta.id, pergunta_id=p.id,
                                           pergunta_texto=p.texto, pergunta_tipo=p.tipo)
            if p.tipo in ('numero', 'escala'):
                try:
                    item.valor_numero = float(valor.replace(',', '.'))
                except ValueError:
                    continue
            else:
                item.valor_texto = valor[:2000]
            db.session.add(item)

        db.session.commit()
        flash('Resposta enviada! Obrigado.', 'success')
        return redirect(url_for('formularios'))

    return render_template('formulario_responder.html', formulario=f, perguntas=perguntas,
                           valores_existentes=valores_existentes, ja_respondeu=bool(resposta_existente))

@app.route('/formularios/<int:id>/indicadores')
@admin_required
def formulario_indicadores(id):
    f = Formulario.query.get_or_404(id)
    perguntas = FormularioPergunta.query.filter_by(formulario_id=f.id).order_by(FormularioPergunta.ordem).all()
    colaborador_id = request.args.get('colaborador', type=int)

    respostas_q = FormularioResposta.query.filter_by(formulario_id=f.id)
    if colaborador_id:
        respostas_q = respostas_q.filter_by(user_id=colaborador_id)
    respostas = respostas_q.order_by(FormularioResposta.enviado_em.desc()).all()
    resposta_ids = [r.id for r in respostas]

    colaboradores = User.query.join(FormularioResposta, FormularioResposta.user_id == User.id)\
        .filter(FormularioResposta.formulario_id == f.id).distinct().order_by(User.username).all()

    indicadores = []
    for p in perguntas:
        if resposta_ids:
            itens = FormularioRespostaItem.query.filter_by(pergunta_id=p.id)\
                .filter(FormularioRespostaItem.resposta_id.in_(resposta_ids)).all()
        else:
            itens = []
        ind = {'pergunta': p, 'total_respostas': len(itens)}
        if p.tipo in ('numero', 'escala'):
            valores = [i.valor_numero for i in itens if i.valor_numero is not None]
            ind['media'] = round(sum(valores) / len(valores), 2) if valores else None
            distrib = {}
            for v in valores:
                chave = int(v) if float(v).is_integer() else v
                distrib[chave] = distrib.get(chave, 0) + 1
            ind['distribuicao'] = sorted(distrib.items())
        elif p.tipo in ('multipla_escolha', 'sim_nao'):
            contagem = {}
            for i in itens:
                if i.valor_texto:
                    contagem[i.valor_texto] = contagem.get(i.valor_texto, 0) + 1
            ind['distribuicao'] = sorted(contagem.items(), key=lambda x: -x[1])
        else:
            ind['respostas_texto'] = sorted([
                {'texto': i.valor_texto, 'colaborador': i.resposta.colaborador, 'data': i.resposta.enviado_em}
                for i in itens if i.valor_texto
            ], key=lambda x: x['data'], reverse=True)[:200]
        indicadores.append(ind)

    return render_template('formulario_indicadores.html', formulario=f, indicadores=indicadores,
                           colaboradores=colaboradores, colaborador_selecionado=colaborador_id,
                           total_respostas=len(respostas), respostas=respostas)

@app.route('/formularios/<int:form_id>/respostas/<int:resposta_id>/excluir', methods=['POST'])
@admin_required
def formulario_resposta_excluir(form_id, resposta_id):
    """Exclui a resposta de UM colaborador (não o formulário inteiro) — pra
    tirar do indicador quem respondeu por engano, saiu da equipe etc."""
    resposta = FormularioResposta.query.filter_by(id=resposta_id, formulario_id=form_id).first_or_404()
    nome = nome_exibicao(resposta.colaborador)
    FormularioRespostaItem.query.filter_by(resposta_id=resposta.id).delete()
    db.session.delete(resposta)
    db.session.commit()
    log_action(session['user_id'], session['username'], 'excluir', 'formulario_resposta', resposta_id,
               f'resposta de {nome} no formulário #{form_id}')
    flash(f'Resposta de {nome} excluída.', 'success')
    return redirect(url_for('formulario_indicadores', id=form_id))

@app.route('/formularios/<int:id>/exportar')
@admin_required
def formulario_exportar(id):
    f = Formulario.query.get_or_404(id)
    perguntas = FormularioPergunta.query.filter_by(formulario_id=f.id).order_by(FormularioPergunta.ordem).all()
    respostas = FormularioResposta.query.filter_by(formulario_id=f.id).order_by(FormularioResposta.enviado_em).all()

    import openpyxl
    from openpyxl.styles import Font, PatternFill, Alignment
    from openpyxl.utils import get_column_letter

    wb = openpyxl.Workbook()
    ws = wb.active
    ws.title = 'Respostas'

    cabecalho = ['Colaborador', 'Enviado em'] + [
        p.texto + (' (inativa)' if not p.ativa else '') for p in perguntas
    ]
    ws.append(cabecalho)
    for col in range(1, len(cabecalho) + 1):
        c = ws.cell(row=1, column=col)
        c.font = Font(bold=True, color='FFFFFF')
        c.fill = PatternFill('solid', fgColor='F2780D')
        c.alignment = Alignment(wrap_text=True, vertical='center')

    for r in respostas:
        itens_por_pergunta = {i.pergunta_id: i for i in FormularioRespostaItem.query.filter_by(resposta_id=r.id).all()}
        linha = [nome_exibicao(r.colaborador), r.enviado_em.strftime('%d/%m/%Y %H:%M')]
        for p in perguntas:
            item = itens_por_pergunta.get(p.id)
            if not item:
                linha.append('')
            elif item.valor_numero is not None:
                linha.append(item.valor_numero)
            else:
                linha.append(item.valor_texto or '')
        ws.append(linha)

    for col in range(1, len(cabecalho) + 1):
        ws.column_dimensions[get_column_letter(col)].width = 26

    buf = io.BytesIO()
    wb.save(buf)
    buf.seek(0)
    return send_file(buf, mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
                      as_attachment=True, download_name=f'formulario_{f.id}_respostas.xlsx')

# ─── CALENDÁRIO ────────────────────────────────────────────────────────────────

def _mes_ano_ajustado(ano, mes):
    """Normaliza mes/ano pra sempre cair num mês válido (1-12), rolando o ano
    quando a navegação passa de janeiro pra trás ou de dezembro pra frente."""
    if mes < 1:
        return ano - 1, 12
    if mes > 12:
        return ano + 1, 1
    return ano, mes

def _grade_calendario(ano, mes):
    """Monta a grade de semanas do mês (com dias de meses vizinhos pra
    completar a semana) e agrupa as demandas que caem em cada dia da grade —
    usado tanto na tela interna quanto na página pública."""
    semanas = _calendar.Calendar(firstweekday=6).monthdatescalendar(ano, mes)
    primeiro_dia_grade = semanas[0][0]
    ultimo_dia_grade = semanas[-1][-1]

    demandas_mes = Demanda.query.filter(
        Demanda.data_inicio <= ultimo_dia_grade, Demanda.data_fim >= primeiro_dia_grade
    ).order_by(Demanda.data_inicio).all()

    por_dia = {}
    for d in demandas_mes:
        cursor = max(d.data_inicio, primeiro_dia_grade)
        fim = min(d.data_fim, ultimo_dia_grade)
        while cursor <= fim:
            por_dia.setdefault(cursor, []).append(d)
            cursor += timedelta(days=1)

    return semanas, por_dia, demandas_mes

SEM_MODULO_LABEL = 'Sem módulo'

TRIMESTRE_LABEL = {1: 'Jan-Mar', 2: 'Abr-Jun', 3: 'Jul-Set', 4: 'Out-Dez'}

def _intervalo_trimestre(ano, tri):
    """Intervalo [início, fim) em datas de um trimestre — 1=Jan-Mar, 2=Abr-Jun,
    3=Jul-Set, 4=Out-Dez, de três em três meses a partir de janeiro."""
    mes_ini = (tri - 1) * 3 + 1
    ano_fim, mes_fim = (ano, mes_ini + 3) if mes_ini + 3 <= 12 else (ano + 1, mes_ini + 3 - 12)
    return datetime(ano, mes_ini, 1), datetime(ano_fim, mes_fim, 1)

def _trimestres_disponiveis():
    """Trimestres (ano, nº) em que existe ao menos uma disciplina marcada
    liberada no Moodle — usado pra só oferecer no filtro períodos que têm
    dado de verdade, mais recente primeiro."""
    datas = db.session.query(DisciplinaModulo.status_em).filter(
        DisciplinaModulo.status == 'liberada_moodle', DisciplinaModulo.status_em != None).all()
    pares = {(d.year, (d.month - 1) // 3 + 1) for (d,) in datas if d}
    return sorted(pares, reverse=True)

def _disciplinas_agrupadas(tipo_filtro=None, incluir_arquivadas=False, trimestre_filtro=None):
    """Disciplinas de inserção agrupadas em 2 níveis — Tipo (ex: 'APA CLARA
    IA') e, dentro dele, Módulo (ex: 'Módulo 1') — com a contagem de quantas
    já estão liberadas no Moodle em cada nível. Base do painel interno, da
    página pública, do widget da dashboard e do resumo por Tipo. Por
    padrão não traz as arquivadas (ficam fora sem apagar o dado).
    `trimestre_filtro` (ano, trimestre) restringe a só as liberadas no
    Moodle dentro daquele período — as demais ficam fora da listagem."""
    q = DisciplinaModulo.query
    if not incluir_arquivadas:
        q = q.filter_by(arquivado=False)
    if tipo_filtro:
        q = q.filter_by(modulo=tipo_filtro)
    if trimestre_filtro:
        inicio, fim = _intervalo_trimestre(*trimestre_filtro)
        q = q.filter(DisciplinaModulo.status == 'liberada_moodle',
                     DisciplinaModulo.status_em >= inicio, DisciplinaModulo.status_em < fim)
    disciplinas = q.order_by(DisciplinaModulo.modulo, DisciplinaModulo.submodulo,
                              DisciplinaModulo.ordem, DisciplinaModulo.nome).all()

    tipos = {}
    for d in disciplinas:
        tipos.setdefault(d.modulo, {}).setdefault(d.submodulo or SEM_MODULO_LABEL, []).append(d)

    resultado = []
    for tipo_nome in sorted(tipos.keys(), key=lambda s: s.lower()):
        submodulos_dict = tipos[tipo_nome]
        submodulos = []
        total_tipo = 0
        liberadas_tipo = 0
        for sub_nome in sorted(submodulos_dict.keys(), key=lambda s: (s == SEM_MODULO_LABEL, s.lower())):
            itens_originais = submodulos_dict[sub_nome]
            # agrupa por status pra facilitar a visualização — liberadas (Moodle
            # ou Inova) sempre no topo, a mais recente liberada na frente das
            # outras; depois vêm os outros status juntos, do mais avançado no
            # processo pro menos avançado, cada um mantendo entre si a ordem de
            # sempre (ordem/nome).
            baldes = {}
            for i in itens_originais:
                baldes.setdefault(_PRIORIDADE_STATUS_LISTAGEM.get(i.status, 99), []).append(i)
            itens = []
            for prioridade in sorted(baldes.keys()):
                grupo = baldes[prioridade]
                if prioridade == 0:
                    grupo = sorted(grupo, key=lambda i: i.status_em or datetime.min, reverse=True)
                itens.extend(grupo)
            liberadas = sum(1 for i in itens if i.status in ('liberada_moodle', 'liberada_inova'))
            linhas_texto = '\n'.join(
                '\t'.join([i.nome, i.carga or '', i.professor or '']).rstrip('\t')
                for i in itens
            )
            submodulos.append({'submodulo': sub_nome, 'itens': itens, 'liberadas': liberadas, 'total': len(itens),
                                'linhas_texto': linhas_texto})
            total_tipo += len(itens)
            liberadas_tipo += liberadas
        por_status_tipo = {}
        for sub in submodulos:
            for it in sub['itens']:
                por_status_tipo[it.status] = por_status_tipo.get(it.status, 0) + 1
        resultado.append({'tipo': tipo_nome, 'submodulos': submodulos, 'total': total_tipo,
                           'liberadas': liberadas_tipo, 'por_status': por_status_tipo})
    return resultado

def _resumo_de_tipo(grupo):
    """Resumo (total/pendentes/liberadas/por etapa) de um grupo de
    _disciplinas_agrupadas — usado no Dashboard interno e no público."""
    return {'nome': grupo['tipo'], 'total': grupo['total'], 'liberadas': grupo['liberadas'],
            'pendentes': grupo['total'] - grupo['liberadas'], 'por_status': grupo['por_status']}

def _calendario_publico_ativo():
    setting = AppSetting.query.get('calendario_publico_ativo')
    if setting is None or setting.value is None:
        return True  # ligado por padrão até o admin desligar
    return setting.value == '1'

def _voltar_seguro(default):
    """Le o campo voltar_para do POST (a pagina do Calendario de onde a
    acao partiu - aba, mes, filtros) e volta pra la em vez de sempre cair
    na aba padrao. So aceita caminho relativo interno (nunca um dominio
    externo colado nesse campo) - se nao vier nada valido, usa o default."""
    destino = (request.form.get('voltar_para') or '').strip()
    if destino.startswith('/') and not destino.startswith('//') and '\\' not in destino:
        return destino
    return default

def _voltar_calendario(default, **overrides):
    """Igual _voltar_seguro, mas permite sobrescrever/acrescentar parametros
    na query de volta — usado quando criar/editar uma demanda precisa pular
    pro mes dela, sem perder a aba (calendario/lista) de onde a acao partiu."""
    destino = _voltar_seguro(default)
    if not overrides:
        return destino
    partes = urlsplit(destino)
    query = parse_qs(partes.query)
    for chave, valor in overrides.items():
        query[chave] = [str(valor)]
    nova_query = urlencode(query, doseq=True)
    return urlunsplit((partes.scheme, partes.netloc, partes.path, nova_query, partes.fragment))

def _responsaveis_validos_ids(form):
    """ids de responsável postados que realmente pertencem à equipe de
    inserção — qualquer id fora dessa lista é ignorado (defesa extra além
    do <select> só mostrar essas opções)."""
    permitidos = {u.id for u in _usuarios_equipe_insercao()}
    postados = [int(x) for x in form.getlist('responsavel_ids') if x.isdigit()]
    return [x for x in postados if x in permitidos]

@app.route('/calendario')
@perm_check('can_view_calendario')
def calendario():
    hoje = date.today()
    ano, mes = _mes_ano_ajustado(request.args.get('ano', type=int) or hoje.year,
                                  request.args.get('mes', type=int) or hoje.month)
    semanas, por_dia, demandas_mes = _grade_calendario(ano, mes)

    status_filtro = request.args.get('status') or ''
    responsavel_filtro = request.args.get('responsavel', type=int)
    lista_q = Demanda.query
    if status_filtro in STATUS_DEMANDA:
        lista_q = lista_q.filter_by(status=status_filtro)
    lista_demandas = lista_q.order_by(Demanda.data_fim).all()
    if responsavel_filtro:
        lista_demandas = [d for d in lista_demandas if responsavel_filtro in d.responsaveis_ids()]

    usuarios = _usuarios_equipe_insercao()
    u = User.query.get(session['user_id'])

    demandas_json = {
        d.id: {
            'id': d.id, 'titulo': d.titulo, 'descricao': d.descricao or '',
            'data_inicio': d.data_inicio.isoformat(), 'data_fim': d.data_fim.isoformat(),
            'status': d.status, 'responsavel_ids': d.responsaveis_ids(),
            'pode_editar': d.pode_editar(u),
            'pode_registrar_status': d.pode_registrar_status(u),
            'alerta_ativo': d.alerta_ativo, 'alerta_texto': d.alerta_texto or '',
            'alerta_whatsapp': d.alerta_whatsapp,
        }
        for d in set(demandas_mes) | set(lista_demandas)
    }

    ano_ant, mes_ant = _mes_ano_ajustado(ano, mes - 1)
    ano_prox, mes_prox = _mes_ano_ajustado(ano, mes + 1)

    aba = request.args.get('aba') if request.args.get('aba') in ('calendario', 'lista', 'disciplinas', 'dashboard', 'alertas') else 'disciplinas'

    meus_lembretes = []
    if aba == 'alertas':
        meus_lembretes = [
            _lembrete_para_exibir(l)
            for l in LembreteFixo.query.filter_by(user_id=u.id).order_by(LembreteFixo.dia_mes).all()
        ]
    tem_whatsapp = bool(u.telefone_whatsapp)
    try:
        whatsapp_prefs = json.loads(u.whatsapp_prefs or '{}')
    except (ValueError, TypeError):
        whatsapp_prefs = {}
    tipo_detalhe = request.args.get('tipo') or ''  # nome do Tipo selecionado — mostra o resumo só dele
    ver_arquivadas = request.args.get('arquivadas') == '1'
    trimestre_param = request.args.get('trimestre') or ''
    trimestre_filtro = None
    if '-' in trimestre_param:
        try:
            ano_t, tri_t = trimestre_param.split('-')
            trimestre_filtro = (int(ano_t), int(tri_t))
        except ValueError:
            trimestre_param = ''
    modulos = _disciplinas_agrupadas(tipo_detalhe or None, incluir_arquivadas=ver_arquivadas,
                                      trimestre_filtro=trimestre_filtro)
    trimestres_disponiveis = [
        {'valor': f'{ano}-{tri}', 'label': f'{TRIMESTRE_LABEL[tri]}/{ano}'}
        for ano, tri in _trimestres_disponiveis()
    ]

    total_arquivadas_q = DisciplinaModulo.query.filter_by(arquivado=True)
    if tipo_detalhe:
        total_arquivadas_q = total_arquivadas_q.filter_by(modulo=tipo_detalhe)
    total_arquivadas = total_arquivadas_q.count() if not ver_arquivadas else sum(g['total'] for g in modulos)

    total_disc_geral = sum(g['total'] for g in modulos)
    liberadas_disc_geral = sum(g['liberadas'] for g in modulos)
    pronto_percentual = round(liberadas_disc_geral / total_disc_geral * 100, 1) if total_disc_geral else 0

    tipo_resumo = None
    todos_tipos_resumo = []
    if aba == 'dashboard':
        if tipo_detalhe and modulos:
            tipo_resumo = _resumo_de_tipo(modulos[0])
        else:
            todos_tipos_resumo = [_resumo_de_tipo(g) for g in _disciplinas_agrupadas(incluir_arquivadas=ver_arquivadas)]

    modulos_cadastrados = ModuloCalendario.query.order_by(ModuloCalendario.ordem, ModuloCalendario.nome).all()
    submodulos_cadastrados = SubmoduloCalendario.query.order_by(
        SubmoduloCalendario.ordem, SubmoduloCalendario.nome).all()

    return render_template('calendario.html',
        ano=ano, mes=mes, mes_nome=MESES_PT[mes], semanas=semanas, hoje=hoje, por_dia=por_dia,
        ano_ant=ano_ant, mes_ant=mes_ant, ano_prox=ano_prox, mes_prox=mes_prox,
        lista_demandas=lista_demandas, usuarios=usuarios, status_filtro=status_filtro,
        responsavel_filtro=responsavel_filtro, demandas_json=demandas_json,
        STATUS_DEMANDA=STATUS_DEMANDA, STATUS_LABEL=STATUS_DEMANDA_LABEL,
        aba=aba, modulos=modulos, STATUS_DISC=STATUS_DISC_MODULO, STATUS_DISC_LABEL=STATUS_DISC_MODULO_LABEL,
        STATUS_DISC_COR=STATUS_DISC_MODULO_COR,
        pronto_percentual=pronto_percentual, total_disc_geral=total_disc_geral, liberadas_disc_geral=liberadas_disc_geral,
        modulos_cadastrados=modulos_cadastrados, publico_ativo=_calendario_publico_ativo(),
        submodulos_cadastrados=submodulos_cadastrados,
        trimestre_param=trimestre_param, trimestres_disponiveis=trimestres_disponiveis,
        tipo_detalhe=tipo_detalhe, tipo_resumo=tipo_resumo, todos_tipos_resumo=todos_tipos_resumo,
        SEM_MODULO_LABEL=SEM_MODULO_LABEL,
        ver_arquivadas=ver_arquivadas, total_arquivadas=total_arquivadas,
        meus_lembretes=meus_lembretes, tem_whatsapp=tem_whatsapp, whatsapp_prefs=whatsapp_prefs,
        telefone_whatsapp=u.telefone_whatsapp or '', whatsapp_apikey=u.whatsapp_apikey or '',
        agenda_ics_url=u.agenda_ics_url or '',
        agenda_ics_visibilidade=u.agenda_ics_visibilidade or 'pessoal',
        is_admin=(u.role == 'admin'))

@app.route('/calendario/publico')
def calendario_publico():
    """Página pública, sem login — pra compartilhar com quem precisa
    acompanhar de fora: só a listagem (disciplinas por módulo e as
    demandas), sem grade de calendário, tudo na mesma tela em abas. Admin
    pode desligar em /calendario, sem precisar mexer em código."""
    if not _calendario_publico_ativo():
        return render_template('calendario_publico_desativado.html'), 200

    # Link pode vir filtrado pra um só Tipo (ex: ?tipo=PÓS), pra compartilhar
    # com um stakeholder específico sem ele ver o andamento dos outros tipos.
    tipo_filtro = request.args.get('tipo') or ''

    demandas = Demanda.query.order_by(Demanda.data_fim).all()
    demandas_view = [{
        'titulo': d.titulo, 'descricao': d.descricao or '',
        'data_inicio': d.data_inicio.strftime('%d/%m/%Y'), 'data_fim': d.data_fim.strftime('%d/%m/%Y'),
        'status': d.status,
        'responsavel': ', '.join(nome_exibicao(r) for r in d.responsaveis_usuarios()) or None,
    } for d in demandas]
    modulos = _disciplinas_agrupadas(tipo_filtro or None)
    todos_tipos_resumo = [_resumo_de_tipo(g) for g in modulos]
    total_disc_geral = sum(g['total'] for g in modulos)
    liberadas_disc_geral = sum(g['liberadas'] for g in modulos)
    pronto_percentual = round(liberadas_disc_geral / total_disc_geral * 100, 1) if total_disc_geral else 0

    return render_template('calendario_publico.html',
        demandas=demandas_view, modulos=modulos, todos_tipos_resumo=todos_tipos_resumo,
        tipo_filtro=tipo_filtro,
        pronto_percentual=pronto_percentual, total_disc_geral=total_disc_geral, liberadas_disc_geral=liberadas_disc_geral,
        STATUS_LABEL=STATUS_DEMANDA_LABEL, STATUS_DISC=STATUS_DISC_MODULO,
        STATUS_DISC_LABEL=STATUS_DISC_MODULO_LABEL, STATUS_DISC_COR=STATUS_DISC_MODULO_COR)

@app.route('/calendario/publico/toggle', methods=['POST'])
@admin_required
def calendario_publico_toggle():
    novo = not _calendario_publico_ativo()
    setting = AppSetting.query.get('calendario_publico_ativo')
    if not setting:
        setting = AppSetting(key='calendario_publico_ativo')
        db.session.add(setting)
    setting.value = '1' if novo else '0'
    db.session.commit()
    flash('Link público ativado!' if novo else 'Link público desativado — quem tiver o link vê um aviso.', 'success')
    return redirect(_voltar_seguro(url_for('calendario')))

@app.route('/calendario/nova', methods=['POST'])
@admin_required
def calendario_nova():
    d = request.form
    titulo = (d.get('titulo') or '').strip()
    data_inicio = _parse_data_form(d.get('data_inicio'))
    data_fim = _parse_data_form(d.get('data_fim'))
    if not titulo or not data_inicio or not data_fim:
        flash('Preencha título, início e prazo da demanda.', 'danger')
        return redirect(_voltar_seguro(url_for('calendario', aba='calendario')))
    if data_fim < data_inicio:
        flash('O prazo não pode ser antes do início.', 'danger')
        return redirect(_voltar_seguro(url_for('calendario', aba='calendario')))
    status = d.get('status') if d.get('status') in STATUS_DEMANDA else 'andamento'
    responsaveis_ids = _responsaveis_validos_ids(d)
    demanda = Demanda(titulo=titulo, descricao=(d.get('descricao') or '').strip() or None,
                       data_inicio=data_inicio, data_fim=data_fim, status=status,
                       responsaveis=','.join(str(x) for x in responsaveis_ids) or None,
                       created_by=session['user_id'])
    db.session.add(demanda)
    db.session.commit()
    log_action(session['user_id'], session['username'], 'criar', 'demanda', demanda.id, demanda.titulo)
    flash('Demanda adicionada ao calendário!', 'success')
    return redirect(_voltar_calendario(url_for('calendario', aba='calendario', ano=data_inicio.year, mes=data_inicio.month),
                                        ano=data_inicio.year, mes=data_inicio.month))

@app.route('/calendario/<int:id>/editar', methods=['POST'])
@admin_required
def calendario_editar(id):
    demanda = Demanda.query.get_or_404(id)
    d = request.form
    titulo = (d.get('titulo') or '').strip()
    data_inicio = _parse_data_form(d.get('data_inicio'))
    data_fim = _parse_data_form(d.get('data_fim'))
    if not titulo or not data_inicio or not data_fim or data_fim < data_inicio:
        flash('Dados inválidos — confira título, início e prazo.', 'danger')
        return redirect(_voltar_seguro(url_for('calendario', aba='calendario')))
    demanda.titulo = titulo
    demanda.descricao = (d.get('descricao') or '').strip() or None
    demanda.data_inicio = data_inicio
    demanda.data_fim = data_fim
    demanda.responsaveis = ','.join(str(x) for x in _responsaveis_validos_ids(d)) or None
    if d.get('status') in STATUS_DEMANDA:
        demanda.status = d.get('status')
    db.session.commit()
    log_action(session['user_id'], session['username'], 'editar', 'demanda', demanda.id, demanda.titulo)
    flash('Demanda atualizada!', 'success')
    return redirect(_voltar_calendario(url_for('calendario', aba='calendario', ano=data_inicio.year, mes=data_inicio.month),
                                        ano=data_inicio.year, mes=data_inicio.month))

@app.route('/calendario/<int:id>/excluir', methods=['POST'])
@admin_required
def calendario_excluir(id):
    demanda = Demanda.query.get_or_404(id)
    titulo = demanda.titulo
    DemandaAlertaDispensa.query.filter_by(demanda_id=id).delete()
    db.session.delete(demanda)
    db.session.commit()
    log_action(session['user_id'], session['username'], 'excluir', 'demanda', id, titulo)
    flash('Demanda excluída.', 'success')
    return redirect(_voltar_seguro(url_for('calendario', aba='calendario')))

@app.route('/calendario/<int:id>/status', methods=['POST'])
@perm_check('can_view_calendario')
def calendario_status(id):
    demanda = Demanda.query.get_or_404(id)
    u = User.query.get(session['user_id'])
    if not demanda.pode_registrar_status(u):
        flash('Só o admin ou o responsável designado pode registrar o andamento desta demanda.', 'danger')
        return redirect(_voltar_seguro(url_for('calendario', aba='calendario')))
    novo = request.form.get('status')
    if novo in STATUS_DEMANDA:
        demanda.status = novo
        db.session.commit()
        log_action(session['user_id'], session['username'], 'editar', 'demanda', demanda.id, f'status -> {novo}')
    return redirect(_voltar_seguro(url_for('calendario', aba='calendario')))

@app.route('/calendario/<int:id>/alertar', methods=['POST'])
@perm_check('can_view_calendario')
def calendario_alertar(id):
    """Dispara (ou atualiza) o aviso manual dessa Demanda pra equipe toda —
    mesma permissão de registrar andamento. Limpa as dispensas antigas, pra
    quem já tinha fechado o aviso anterior ver esse de novo."""
    demanda = Demanda.query.get_or_404(id)
    u = User.query.get(session['user_id'])
    if not demanda.pode_registrar_status(u):
        flash('Só o admin ou um dos responsáveis pode avisar a equipe sobre esta demanda.', 'danger')
        return redirect(_voltar_seguro(url_for('calendario', aba='lista')))
    texto = (request.form.get('alerta_texto') or '').strip()
    demanda.alerta_ativo = True
    demanda.alerta_texto = texto[:500] or None
    demanda.alerta_criado_em = datetime.utcnow()
    demanda.alerta_criado_por = u.id
    demanda.alerta_whatsapp = request.form.get('alerta_whatsapp') == 'on'
    demanda.alerta_whatsapp_enviado = False
    DemandaAlertaDispensa.query.filter_by(demanda_id=demanda.id).delete()
    db.session.commit()
    log_action(u.id, u.username, 'alertar', 'demanda', demanda.id, demanda.titulo)
    flash('Aviso enviado pra equipe!', 'success')
    return redirect(_voltar_seguro(url_for('calendario', aba='lista')))

@app.route('/calendario/<int:id>/alerta/cancelar', methods=['POST'])
@perm_check('can_view_calendario')
def calendario_alerta_cancelar(id):
    demanda = Demanda.query.get_or_404(id)
    u = User.query.get(session['user_id'])
    if not demanda.pode_registrar_status(u):
        flash('Só o admin ou um dos responsáveis pode retirar este aviso.', 'danger')
        return redirect(_voltar_seguro(url_for('calendario', aba='lista')))
    demanda.alerta_ativo = False
    db.session.commit()
    log_action(u.id, u.username, 'cancelar_alerta', 'demanda', demanda.id, demanda.titulo)
    flash('Aviso retirado.', 'success')
    return redirect(_voltar_seguro(url_for('calendario', aba='lista')))

@app.route('/calendario/<int:id>/alerta/dispensar', methods=['POST'])
@perm_check('can_view_calendario')
def calendario_alerta_dispensar(id):
    """A pessoa clica pra sumir com o aviso — só pra ela; quem não clicou
    continua vendo. Chamado via fetch() pelo sino/aviso, em qualquer tela."""
    Demanda.query.get_or_404(id)
    ja = DemandaAlertaDispensa.query.filter_by(demanda_id=id, user_id=session['user_id']).first()
    if not ja:
        db.session.add(DemandaAlertaDispensa(demanda_id=id, user_id=session['user_id']))
        db.session.commit()
    return jsonify({'ok': True})

@app.route('/calendario/lembretes/novo', methods=['POST'])
@perm_check('can_view_calendario')
def calendario_lembrete_novo():
    """Lembrete mensal fixo e pessoal — cada um cadastra o seu; nem admin
    vê o lembrete de outra pessoa."""
    titulo = (request.form.get('titulo') or '').strip()
    dia_mes = request.form.get('dia_mes', type=int)
    if not titulo or not dia_mes or not (1 <= dia_mes <= 31):
        flash('Preencha o título e um dia do mês válido (1 a 31).', 'danger')
        return redirect(_voltar_seguro(url_for('calendario', aba='alertas')))
    db.session.add(LembreteFixo(user_id=session['user_id'], titulo=titulo[:200], dia_mes=dia_mes,
                                 avisar_whatsapp=request.form.get('avisar_whatsapp') == 'on'))
    db.session.commit()
    flash('Lembrete adicionado!', 'success')
    return redirect(_voltar_seguro(url_for('calendario', aba='alertas')))

@app.route('/calendario/lembretes/<int:id>/editar', methods=['POST'])
@perm_check('can_view_calendario')
def calendario_lembrete_editar(id):
    lembrete = LembreteFixo.query.get_or_404(id)
    if lembrete.user_id != session['user_id']:
        flash('Você só pode editar os seus próprios lembretes.', 'danger')
        return redirect(_voltar_seguro(url_for('calendario', aba='alertas')))
    titulo = (request.form.get('titulo') or '').strip()
    dia_mes = request.form.get('dia_mes', type=int)
    if not titulo or not dia_mes or not (1 <= dia_mes <= 31):
        flash('Preencha o título e um dia do mês válido (1 a 31).', 'danger')
        return redirect(_voltar_seguro(url_for('calendario', aba='alertas')))
    lembrete.titulo = titulo[:200]
    lembrete.dia_mes = dia_mes
    lembrete.avisar_whatsapp = request.form.get('avisar_whatsapp') == 'on'
    db.session.commit()
    flash('Lembrete atualizado!', 'success')
    return redirect(_voltar_seguro(url_for('calendario', aba='alertas')))

@app.route('/calendario/lembretes/<int:id>/concluir', methods=['POST'])
@perm_check('can_view_calendario')
def calendario_lembrete_concluir(id):
    """A pessoa clica em "Já fiz isso" — grava a ocorrência atual como
    confirmada, e o aviso some até o próximo mês. Chamado via fetch() tanto
    pelo aviso no topo (qualquer tela) quanto pela lista da aba Alertas."""
    lembrete = LembreteFixo.query.get_or_404(id)
    if lembrete.user_id != session['user_id']:
        return jsonify({'ok': False, 'erro': 'Este lembrete não é seu.'}), 403
    pend = _lembrete_pendencia(lembrete)
    lembrete.ultimo_checkin_ocorrencia = pend['ocorrencia'] if pend else date.today()
    db.session.commit()
    return jsonify({'ok': True})

@app.route('/calendario/lembretes/<int:id>/excluir', methods=['POST'])
@perm_check('can_view_calendario')
def calendario_lembrete_excluir(id):
    lembrete = LembreteFixo.query.get_or_404(id)
    if lembrete.user_id != session['user_id']:
        flash('Você só pode excluir os seus próprios lembretes.', 'danger')
        return redirect(_voltar_seguro(url_for('calendario', aba='alertas')))
    db.session.delete(lembrete)
    db.session.commit()
    flash('Lembrete removido.', 'success')
    return redirect(_voltar_seguro(url_for('calendario', aba='alertas')))

# ─── CALENDÁRIO — DISCIPLINAS POR MÓDULO (inserção) ─────────────────────────────

@app.route('/calendario/disciplinas/nova', methods=['POST'])
@admin_required
def calendario_disciplina_nova():
    d = request.form
    tipo = (d.get('modulo') or '').strip()
    nome = (d.get('nome') or '').strip()
    if not tipo or not nome:
        flash('Preencha o tipo e o nome da disciplina.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    item = DisciplinaModulo(modulo=tipo, submodulo=(d.get('submodulo') or '').strip() or None, nome=nome,
                             carga=(d.get('carga') or '').strip() or None,
                             professor=(d.get('professor') or '').strip() or None,
                             observacao=(d.get('observacao') or '').strip() or None,
                             created_by=session['user_id'])
    db.session.add(item)
    db.session.commit()
    log_action(session['user_id'], session['username'], 'criar', 'disciplina_modulo', item.id, f'{tipo} — {nome}')
    flash('Disciplina adicionada!', 'success')
    return redirect(url_for('calendario', aba='disciplinas'))

@app.route('/calendario/disciplinas/<int:id>/editar', methods=['POST'])
@admin_required
def calendario_disciplina_editar(id):
    item = DisciplinaModulo.query.get_or_404(id)
    d = request.form
    tipo = (d.get('modulo') or '').strip()
    nome = (d.get('nome') or '').strip()
    if not tipo or not nome:
        flash('Preencha o tipo e o nome da disciplina.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    item.modulo = tipo
    item.submodulo = (d.get('submodulo') or '').strip() or None
    item.nome = nome
    item.carga = (d.get('carga') or '').strip() or None
    item.professor = (d.get('professor') or '').strip() or None
    item.observacao = (d.get('observacao') or '').strip() or None
    db.session.commit()
    log_action(session['user_id'], session['username'], 'editar', 'disciplina_modulo', item.id, f'{tipo} — {nome}')
    flash('Disciplina atualizada!', 'success')
    return redirect(url_for('calendario', aba='disciplinas'))

@app.route('/calendario/disciplinas/<int:id>/excluir', methods=['POST'])
@admin_required
def calendario_disciplina_excluir(id):
    item = DisciplinaModulo.query.get_or_404(id)
    detalhe = f'{item.modulo} — {item.nome}'
    db.session.delete(item)
    db.session.commit()
    log_action(session['user_id'], session['username'], 'excluir', 'disciplina_modulo', id, detalhe)
    flash('Disciplina excluída.', 'success')
    return redirect(url_for('calendario', aba='disciplinas'))

@app.route('/calendario/disciplinas/<int:id>/arquivar', methods=['POST'])
@admin_required
def calendario_disciplina_arquivar(id):
    """Tira uma disciplina da listagem ativa sem apagar o dado — pra não
    ocupar espaço visual depois que o módulo/ano já foi concluído."""
    item = DisciplinaModulo.query.get_or_404(id)
    item.arquivado = not item.arquivado
    db.session.commit()
    flash('Disciplina arquivada.' if item.arquivado else 'Disciplina restaurada.', 'success')
    destino = _voltar_seguro(url_for('calendario', aba='disciplinas'))
    return redirect(destino)

@app.route('/calendario/disciplinas/<int:id>/status', methods=['POST'])
@perm_check('can_view_calendario')
def calendario_disciplina_status(id):
    """Registrar em que etapa a disciplina está — aberto pra qualquer um da
    equipe (é o trabalho do dia a dia), diferente de criar/editar/excluir a
    disciplina em si, que é 'configuração' e fica só com o admin."""
    item = DisciplinaModulo.query.get_or_404(id)
    novo = request.form.get('status')
    if novo in STATUS_DISC_MODULO:
        item.status = novo
        item.status_em = datetime.utcnow()
        db.session.commit()
        log_action(session['user_id'], session['username'], 'editar', 'disciplina_modulo', item.id,
                   f'{item.modulo} — {item.nome}: status -> {novo}')
    destino = _voltar_seguro(url_for('calendario', aba='disciplinas'))
    return redirect(destino)

@app.route('/calendario/disciplinas/status-lote', methods=['POST'])
@login_required
def calendario_disciplina_status_lote():
    """Aplica o mesmo status a várias disciplinas selecionadas de uma vez —
    mesma permissão de registrar status individual (aberto à equipe)."""
    ids = request.form.getlist('ids', type=int)
    novo = request.form.get('status')
    if not ids or novo not in STATUS_DISC_MODULO:
        flash('Selecione ao menos uma disciplina e um status válido.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    total = DisciplinaModulo.query.filter(DisciplinaModulo.id.in_(ids)).update(
        {'status': novo, 'status_em': datetime.utcnow()}, synchronize_session=False)
    db.session.commit()
    log_action(session['user_id'], session['username'], 'editar', 'disciplina_modulo', 0,
               f'status em lote -> {novo} ({total} disciplina(s))')
    flash(f'{total} disciplina(s) atualizada(s) para "{STATUS_DISC_MODULO_LABEL.get(novo, novo)}".', 'success')
    destino = _voltar_seguro(url_for('calendario', aba='disciplinas'))
    return redirect(destino)

@app.route('/calendario/disciplinas/marcar-liberadas', methods=['POST'])
@admin_required
def calendario_disciplinas_marcar_liberadas():
    """Cola uma lista de nomes de disciplinas — busca o nome (sem acento/
    maiúsculas) nas disciplinas cadastradas e aplica o status escolhido em
    todas de uma vez (Stand-by, Em Andamento, Inserida, Liberada no Moodle
    ou Liberada no Inova). Por padrão procura em qualquer Tipo/Módulo, mas
    Tipo e Módulo são opcionais no formulário — se informados, restringe a
    busca a eles, pra evitar acertar por engano uma disciplina de nome
    igual que exista em outro Tipo/Módulo."""
    nomes = [l.strip() for l in (request.form.get('linhas') or '').splitlines() if l.strip()]
    if not nomes:
        flash('Cole ao menos um nome de disciplina.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    status_alvo = request.form.get('status') or ''
    if status_alvo not in STATUS_DISC_MODULO or status_alvo in ('nao_iniciado', 'em_curadoria'):
        status_alvo = 'liberada_moodle'
    modulo = (request.form.get('modulo') or '').strip()
    submodulo = (request.form.get('submodulo') or '').strip()

    # tira nomes repetidos na própria lista colada (mantém o 1º jeito escrito)
    vistos_norm = set()
    nomes_unicos = []
    for n in nomes:
        norm = _norm_name(n)
        if norm in vistos_norm:
            continue
        vistos_norm.add(norm)
        nomes_unicos.append(n)

    query = DisciplinaModulo.query.filter_by(arquivado=False)
    if modulo:
        query = query.filter_by(modulo=modulo)
    if submodulo:
        query = query.filter_by(submodulo=submodulo)
    candidatas_por_norm = {}
    for d in query.all():
        candidatas_por_norm.setdefault(_norm_name(d.nome), []).append(d)

    # pra não criar duplicata "no Tipo errado": antes de criar uma disciplina
    # nova, olha em TODA a base (sem filtro de Tipo/Módulo) se ela já existe
    # em outro lugar — se existir, avisa em vez de criar.
    todas_por_norm = None
    if modulo:
        todas_por_norm = {}
        for d in DisciplinaModulo.query.filter_by(arquivado=False).all():
            todas_por_norm.setdefault(_norm_name(d.nome), []).append(d)

    alteradas = 0
    inseridas = 0
    sem_tipo_pra_criar = 0
    existentes_em_outro_tipo = []  # [(nome_colado, "Tipo / Módulo"), ...]
    agora = datetime.utcnow()
    for nome in nomes_unicos:
        norm = _norm_name(nome)
        achadas = candidatas_por_norm.get(norm)
        if achadas:
            for d in achadas:
                d.status = status_alvo
                d.status_em = agora
                alteradas += 1
            continue
        if not modulo:
            sem_tipo_pra_criar += 1
            continue
        outras = todas_por_norm.get(norm)
        if outras:
            for d in outras:
                onde = d.modulo + (f' / {d.submodulo}' if d.submodulo else '')
                existentes_em_outro_tipo.append(f'{nome} (está em "{onde}")')
            continue
        db.session.add(DisciplinaModulo(modulo=modulo, submodulo=submodulo or None, nome=nome,
                                         status=status_alvo, status_em=agora, created_by=session['user_id']))
        inseridas += 1
    db.session.commit()

    escopo = f' em "{modulo}"' + (f' / "{submodulo}"' if submodulo else '') if modulo else ''
    status_label = STATUS_DISC_MODULO_LABEL.get(status_alvo, status_alvo)
    total_unicos = len(nomes_unicos)
    log_action(session['user_id'], session['username'], 'editar', 'disciplina_modulo', 0,
               f'status em massa via colar lista -> {status_alvo}{escopo} — {inseridas} inserida(s), '
               f'{alteradas} alterada(s), de {total_unicos} nome(s) colado(s) (únicos)'
               + (f', {sem_tipo_pra_criar} não encontrada(s) sem Tipo escolhido pra criar' if sem_tipo_pra_criar else '')
               + (f', {len(existentes_em_outro_tipo)} já existiam em outro Tipo (não criadas)' if existentes_em_outro_tipo else ''))

    partes = []
    if inseridas:
        partes.append(f'{inseridas} disciplina(s) nova(s) inserida(s) já como "{status_label}"')
    if alteradas:
        partes.append(f'{alteradas} tiveram o status alterado para "{status_label}"')
    if not partes:
        msg = f'Nenhuma disciplina encontrada{escopo} entre os {total_unicos} nome(s) colado(s).'
        if sem_tipo_pra_criar:
            msg += ' Escolha um Tipo pra criar automaticamente as que não existem ainda.'
        flash(msg, 'warning')
    else:
        msg = ', '.join(partes) + escopo + '.'
        if sem_tipo_pra_criar:
            msg += f' {sem_tipo_pra_criar} não encontrada(s) e não criada(s) (escolha um Tipo pra criar automaticamente).'
        flash(msg, 'success')
    if existentes_em_outro_tipo:
        flash('Não criadas por já existirem em outro Tipo/Módulo (confira se selecionou o Tipo certo): '
              + '; '.join(existentes_em_outro_tipo), 'warning')
    return redirect(url_for('calendario', aba='disciplinas'))

@app.route('/calendario/exportar')
@perm_check('can_view_calendario')
def calendario_exportar():
    q = Demanda.query
    status_filtro = request.args.get('status') or ''
    responsavel_filtro = request.args.get('responsavel', type=int)
    if status_filtro in STATUS_DEMANDA:
        q = q.filter_by(status=status_filtro)
    demandas = q.order_by(Demanda.data_fim).all()
    if responsavel_filtro:
        demandas = [d for d in demandas if responsavel_filtro in d.responsaveis_ids()]

    import openpyxl
    from openpyxl.styles import Font, PatternFill, Alignment
    from openpyxl.utils import get_column_letter

    wb = openpyxl.Workbook()
    ws = wb.active
    ws.title = 'Demandas'

    cabecalho = ['Demanda', 'Descrição', 'Responsável', 'Início', 'Prazo', 'Andamento', 'Criado por', 'Criado em']
    ws.append(cabecalho)
    for col in range(1, len(cabecalho) + 1):
        c = ws.cell(row=1, column=col)
        c.font = Font(bold=True, color='FFFFFF')
        c.fill = PatternFill('solid', fgColor='F2780D')
        c.alignment = Alignment(wrap_text=True, vertical='center')

    for d in demandas:
        nomes_resp = ', '.join(nome_exibicao(r) for r in d.responsaveis_usuarios())
        ws.append([
            d.titulo,
            d.descricao or '',
            nomes_resp or '—',
            d.data_inicio.strftime('%d/%m/%Y'),
            d.data_fim.strftime('%d/%m/%Y'),
            STATUS_DEMANDA_LABEL.get(d.status, d.status),
            nome_exibicao(d.autor),
            d.created_at.strftime('%d/%m/%Y %H:%M') if d.created_at else '',
        ])

    for col, w in enumerate([30, 40, 22, 14, 14, 16, 22, 18], start=1):
        ws.column_dimensions[get_column_letter(col)].width = w

    buf = io.BytesIO()
    wb.save(buf)
    buf.seek(0)
    return send_file(buf, mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
                      as_attachment=True, download_name=f'demandas_{date.today().isoformat()}.xlsx')

@app.route('/calendario/disciplinas/exportar')
@perm_check('can_view_calendario')
def calendario_disciplinas_exportar():
    """Exporta a listagem de Disciplinas por Tipo — respeita os mesmos
    filtros da tela (tipo, trimestre de liberação, arquivadas ou não)."""
    tipo_filtro = request.args.get('tipo') or ''
    ver_arquivadas = request.args.get('arquivadas') == '1'
    trimestre_filtro = None
    trimestre_param = request.args.get('trimestre') or ''
    if '-' in trimestre_param:
        try:
            ano_t, tri_t = trimestre_param.split('-')
            trimestre_filtro = (int(ano_t), int(tri_t))
        except ValueError:
            pass

    grupos = _disciplinas_agrupadas(tipo_filtro or None, incluir_arquivadas=ver_arquivadas,
                                     trimestre_filtro=trimestre_filtro)

    import openpyxl
    from openpyxl.styles import Font, PatternFill, Alignment
    from openpyxl.utils import get_column_letter

    wb = openpyxl.Workbook()
    ws = wb.active
    ws.title = 'Disciplinas'

    cabecalho = ['Tipo', 'Módulo', 'Disciplina', 'Carga Horária', 'Professor', 'Andamento',
                 'Liberada em', 'Observação', 'Arquivada']
    ws.append(cabecalho)
    for col in range(1, len(cabecalho) + 1):
        c = ws.cell(row=1, column=col)
        c.font = Font(bold=True, color='FFFFFF')
        c.fill = PatternFill('solid', fgColor='F2780D')
        c.alignment = Alignment(wrap_text=True, vertical='center')

    for grupo in grupos:
        for sub in grupo['submodulos']:
            for it in sub['itens']:
                ws.append([
                    grupo['tipo'],
                    '' if sub['submodulo'] == SEM_MODULO_LABEL else sub['submodulo'],
                    it.nome,
                    it.carga or '',
                    it.professor or '',
                    STATUS_DISC_MODULO_LABEL.get(it.status, it.status),
                    it.status_em.strftime('%d/%m/%Y %H:%M') if it.status == 'liberada_moodle' and it.status_em else '',
                    it.observacao or '',
                    'Sim' if it.arquivado else '',
                ])

    for col, w in enumerate([22, 18, 34, 14, 22, 16, 16, 30, 12], start=1):
        ws.column_dimensions[get_column_letter(col)].width = w

    buf = io.BytesIO()
    wb.save(buf)
    buf.seek(0)
    return send_file(buf, mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
                      as_attachment=True, download_name=f'disciplinas_{date.today().isoformat()}.xlsx')

# ─── CALENDÁRIO — TIPOS, MÓDULOS E IMPORTAÇÃO EM MASSA ──────────────────────────

@app.route('/calendario/tipos/novo', methods=['POST'])
@admin_required
def calendario_tipo_novo():
    nome = (request.form.get('nome') or '').strip()
    if not nome:
        flash('Dê um nome ao tipo.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    if ModuloCalendario.query.filter(db.func.lower(ModuloCalendario.nome) == nome.lower()).first():
        flash('Já existe um tipo com esse nome.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    maior_ordem = db.session.query(db.func.coalesce(db.func.max(ModuloCalendario.ordem), 0)).scalar()
    db.session.add(ModuloCalendario(nome=nome, ordem=maior_ordem + 1, created_by=session['user_id']))
    db.session.commit()
    flash('Tipo adicionado!', 'success')
    return redirect(url_for('calendario', aba='disciplinas'))

@app.route('/calendario/tipos/<int:id>/editar', methods=['POST'])
@admin_required
def calendario_tipo_editar(id):
    tipo = ModuloCalendario.query.get_or_404(id)
    novo_nome = (request.form.get('nome') or '').strip()
    if not novo_nome:
        flash('Dê um nome ao tipo.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    if ModuloCalendario.query.filter(
            db.func.lower(ModuloCalendario.nome) == novo_nome.lower(), ModuloCalendario.id != id).first():
        flash('Já existe um tipo com esse nome.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    nome_antigo = tipo.nome
    tipo.nome = novo_nome
    # cascata: disciplinas que usavam o nome antigo passam a usar o novo
    # (Módulo é uma lista global, não pertence a um Tipo — nada a atualizar nele)
    DisciplinaModulo.query.filter_by(modulo=nome_antigo).update({'modulo': novo_nome})
    db.session.commit()
    flash('Tipo renomeado!', 'success')
    return redirect(url_for('calendario', aba='disciplinas'))

@app.route('/calendario/tipos/<int:id>/excluir', methods=['POST'])
@admin_required
def calendario_tipo_excluir(id):
    tipo = ModuloCalendario.query.get_or_404(id)
    if DisciplinaModulo.query.filter_by(modulo=tipo.nome).first():
        flash('Esse tipo tem disciplinas cadastradas — exclua a listagem ou mova as disciplinas antes de remover o tipo.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    db.session.delete(tipo)
    db.session.commit()
    flash('Tipo excluído.', 'success')
    return redirect(url_for('calendario', aba='disciplinas'))

@app.route('/calendario/tipos/<int:id>/arquivar', methods=['POST'])
@admin_required
def calendario_tipo_arquivar(id):
    """Arquiva (ou restaura) de uma vez todas as disciplinas de um tipo —
    útil quando um tipo/ano inteiro já foi concluído e não precisa mais
    ocupar espaço na listagem ativa."""
    tipo = ModuloCalendario.query.get_or_404(id)
    itens = DisciplinaModulo.query.filter_by(modulo=tipo.nome).all()
    if not itens:
        flash('Esse tipo não tem disciplinas cadastradas.', 'warning')
        return redirect(url_for('calendario', aba='disciplinas'))
    novo_estado = any(not i.arquivado for i in itens)
    for i in itens:
        i.arquivado = novo_estado
    db.session.commit()
    flash(f'Tipo "{tipo.nome}" {"arquivado" if novo_estado else "restaurado"} — {len(itens)} disciplina(s).', 'success')
    return redirect(url_for('calendario', aba='disciplinas'))

@app.route('/calendario/tipos/<int:id>/limpar', methods=['POST'])
@admin_required
def calendario_tipo_limpar(id):
    """Apaga TODAS as disciplinas cadastradas dentro de um tipo (a listagem
    inteira), mas mantém o tipo e os módulos dele — pra poder colar uma
    lista nova sem precisar recriar o tipo do zero."""
    tipo = ModuloCalendario.query.get_or_404(id)
    total = DisciplinaModulo.query.filter_by(modulo=tipo.nome).delete(synchronize_session=False)
    db.session.commit()
    log_action(session['user_id'], session['username'], 'excluir', 'disciplina_modulo',
               0, f'listagem inteira do tipo "{tipo.nome}" apagada — {total} disciplina(s)')
    flash(f'Listagem de "{tipo.nome}" apagada — {total} disciplina(s) removida(s). O tipo continua cadastrado.', 'success')
    return redirect(url_for('calendario', aba='disciplinas'))

@app.route('/calendario/submodulos/novo', methods=['POST'])
@admin_required
def calendario_submodulo_novo():
    """Módulo é uma lista global — cadastra o nome uma vez e ele fica
    disponível pra escolher dentro de qualquer Tipo (as disciplinas de
    cada combinação Tipo+Módulo continuam totalmente independentes)."""
    nome = (request.form.get('nome') or '').strip()
    if not nome:
        flash('Dê um nome ao módulo.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    if SubmoduloCalendario.query.filter(db.func.lower(SubmoduloCalendario.nome) == nome.lower()).first():
        flash('Já existe um módulo com esse nome.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    maior_ordem = db.session.query(db.func.coalesce(db.func.max(SubmoduloCalendario.ordem), 0)).scalar()
    db.session.add(SubmoduloCalendario(nome=nome, ordem=maior_ordem + 1, created_by=session['user_id']))
    db.session.commit()
    flash('Módulo adicionado!', 'success')
    return redirect(url_for('calendario', aba='disciplinas'))

@app.route('/calendario/submodulos/<int:id>/editar', methods=['POST'])
@admin_required
def calendario_submodulo_editar(id):
    sub = SubmoduloCalendario.query.get_or_404(id)
    novo_nome = (request.form.get('nome') or '').strip()
    if not novo_nome:
        flash('Dê um nome ao módulo.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    if SubmoduloCalendario.query.filter(
            db.func.lower(SubmoduloCalendario.nome) == novo_nome.lower(), SubmoduloCalendario.id != id).first():
        flash('Já existe um módulo com esse nome.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    nome_antigo = sub.nome
    sub.nome = novo_nome
    # cascata em qualquer Tipo que já tenha disciplinas nesse módulo
    DisciplinaModulo.query.filter_by(submodulo=nome_antigo).update({'submodulo': novo_nome})
    db.session.commit()
    flash('Módulo renomeado!', 'success')
    return redirect(url_for('calendario', aba='disciplinas'))

@app.route('/calendario/submodulos/<int:id>/excluir', methods=['POST'])
@admin_required
def calendario_submodulo_excluir(id):
    sub = SubmoduloCalendario.query.get_or_404(id)
    if DisciplinaModulo.query.filter_by(submodulo=sub.nome).first():
        flash('Esse módulo tem disciplinas cadastradas (em algum Tipo) — mova ou exclua a listagem antes de remover o módulo.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    db.session.delete(sub)
    db.session.commit()
    flash('Módulo excluído.', 'success')
    return redirect(url_for('calendario', aba='disciplinas'))

@app.route('/calendario/disciplinas/limpar', methods=['POST'])
@admin_required
def calendario_disciplinas_limpar():
    """Apaga as disciplinas de um Tipo+Módulo específico, sem apagar o
    Tipo nem o Módulo — usado no 'Excluir listagem' de cada módulo dentro
    de um tipo (inclusive o balaio 'Sem módulo')."""
    tipo = (request.form.get('modulo') or '').strip()
    submodulo = (request.form.get('submodulo') or '').strip() or None
    if not tipo:
        flash('Tipo não informado.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    total = DisciplinaModulo.query.filter_by(modulo=tipo, submodulo=submodulo).delete(synchronize_session=False)
    db.session.commit()
    log_action(session['user_id'], session['username'], 'excluir', 'disciplina_modulo',
               0, f'listagem de {tipo}' + (f' / {submodulo}' if submodulo else '') + f' apagada — {total} disciplina(s)')
    flash(f'{total} disciplina(s) removida(s). Tipo e módulo continuam cadastrados.', 'success')
    return redirect(url_for('calendario', aba='disciplinas'))

def _parse_linhas_disciplinas(texto):
    """Cada linha vira uma disciplina. Se a linha vier colada direto de uma
    planilha (colunas separadas por TAB), a 1ª coluna é o nome, a 2ª a
    carga horária e a 3ª o professor — as demais colunas são ignoradas.
    Linha sem TAB vira só o nome, como sempre foi."""
    resultado = []
    for linha in (texto or '').splitlines():
        if not linha.strip():
            continue
        partes = [p.strip() for p in linha.split('\t')]
        nome = partes[0][:300]
        if not nome:
            continue
        carga = partes[1][:20] if len(partes) > 1 and partes[1] else None
        professor = partes[2][:200] if len(partes) > 2 and partes[2] else None
        resultado.append((nome, carga, professor))
    return resultado

@app.route('/calendario/disciplinas/importar', methods=['POST'])
@admin_required
def calendario_disciplina_importar():
    """Cola uma lista de disciplinas (uma por linha, ou colada direto de uma
    planilha com colunas separadas por TAB) e cria todas de uma vez no
    tipo/módulo escolhidos — pra não precisar cadastrar uma por uma."""
    tipo = (request.form.get('modulo') or '').strip()
    submodulo = (request.form.get('submodulo') or '').strip() or None
    itens = _parse_linhas_disciplinas(request.form.get('linhas'))
    if not tipo:
        flash('Escolha o tipo antes de importar a lista.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))
    if not itens:
        flash('Cole ao menos uma disciplina, uma por linha.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))

    existentes = {d.nome.strip().lower()
                  for d in DisciplinaModulo.query.filter_by(modulo=tipo, submodulo=submodulo).all()}
    vistos = set()
    criadas = 0
    ignoradas = 0
    for nome, carga, professor in itens:
        chave = nome.strip().lower()
        if chave in existentes or chave in vistos:
            ignoradas += 1
            continue
        vistos.add(chave)
        db.session.add(DisciplinaModulo(modulo=tipo, submodulo=submodulo, nome=nome, carga=carga,
                                         professor=professor, created_by=session['user_id']))
        criadas += 1
    db.session.commit()
    log_action(session['user_id'], session['username'], 'criar', 'disciplina_modulo',
               0, f'importação em massa — {criadas} disciplina(s) em {tipo}' + (f' / {submodulo}' if submodulo else '')
               + (f', {ignoradas} repetida(s) ignorada(s)' if ignoradas else ''))
    if criadas == 0:
        flash(f'Nenhuma disciplina nova — as {ignoradas} da lista já existiam em "{tipo}".', 'warning')
    else:
        msg = f'{criadas} disciplina(s) criada(s) em "{tipo}"!'
        if ignoradas:
            msg += f' ({ignoradas} repetida(s) ignorada(s), já existiam ou vieram duplicadas na lista)'
        flash(msg, 'success')
    return redirect(url_for('calendario', aba='disciplinas'))

@app.route('/calendario/disciplinas/lista/editar', methods=['POST'])
@admin_required
def calendario_disciplinas_lista_editar():
    """Reabre a listagem de um Módulo (ou de um Tipo inteiro, se nenhum
    módulo for passado) como texto editável e, ao salvar, substitui a
    lista inteira pelo texto novo — preserva o andamento (status) de quem
    ficou com o nome exatamente igual ao de antes."""
    tipo = (request.form.get('modulo') or '').strip()
    submodulo_form = request.form.get('submodulo')
    tem_submodulo = submodulo_form is not None
    submodulo = (submodulo_form or '').strip() or None
    if not tipo:
        flash('Tipo não informado.', 'danger')
        return redirect(url_for('calendario', aba='disciplinas'))

    q = DisciplinaModulo.query.filter_by(modulo=tipo)
    if tem_submodulo:
        q = q.filter_by(submodulo=submodulo)
    existentes = q.all()
    status_por_nome = {d.nome.strip().lower(): (d.status, d.status_em) for d in existentes}
    total_antes = len(existentes)
    for d in existentes:
        db.session.delete(d)
    db.session.flush()

    itens = _parse_linhas_disciplinas(request.form.get('linhas'))
    vistos = set()
    repetidas = 0
    novas = 0
    for nome, carga, professor in itens:
        chave = nome.strip().lower()
        if chave in vistos:
            repetidas += 1
            continue
        vistos.add(chave)
        item = DisciplinaModulo(modulo=tipo, submodulo=submodulo, nome=nome, carga=carga,
                                 professor=professor, created_by=session['user_id'])
        anterior = status_por_nome.get(chave)
        if anterior:
            item.status, item.status_em = anterior
        db.session.add(item)
        novas += 1
    db.session.commit()
    log_action(session['user_id'], session['username'], 'editar', 'disciplina_modulo',
               0, f'lista de {tipo}' + (f' / {submodulo}' if submodulo else '') + f' reescrita — {total_antes} -> {novas}'
               + (f' ({repetidas} repetida(s) ignorada(s))' if repetidas else ''))
    msg = f'Lista atualizada: {total_antes} removida(s), {novas} nova(s). Andamento preservado por nome igual.'
    if repetidas:
        msg += f' ({repetidas} repetida(s) na lista colada foram ignoradas)'
    flash(msg, 'success')
    return redirect(url_for('calendario', aba='disciplinas'))

# ─── BACKUP ────────────────────────────────────────────────────────────────────

@app.route('/backup/manual', methods=['POST'])
@admin_required
def backup_manual():
    rec = make_backup(tipo='manual')
    flash(f'Backup manual criado com sucesso! ({round(rec.size_kb, 1)} KB, também enviado por e-mail)', 'success')
    return redirect(url_for('dashboard'))

@app.route('/backup/download/<int:id>')
@admin_required
def backup_download(id):
    rec = BackupRecord.query.get_or_404(id)
    if not rec.conteudo:
        flash('Esse backup é de uma versão antiga do sistema e não tem mais o arquivo disponível.', 'warning')
        return redirect(url_for('backup_lista'))
    return send_file(io.BytesIO(rec.conteudo), mimetype='application/zip',
                      as_attachment=True, download_name=rec.filename)

@app.route('/backup/lista')
@admin_required
def backup_lista():
    bks = BackupRecord.query.order_by(BackupRecord.created_at.desc()).all()
    return render_template('backups.html', bks=bks)

def _executar_restauracao(dados):
    """Cria um backup de segurança do estado atual, depois restaura `dados`.
    Se algo der errado na restauração, desfaz tudo (o backup de segurança já
    ficou salvo antes, então nada se perde de qualquer forma)."""
    seguranca = make_backup(tipo='pre-restore')
    try:
        restaurar_backup(dados)
        db.session.commit()
        return seguranca, None
    except Exception as e:
        db.session.rollback()
        return seguranca, str(e)

@app.route('/backup/<int:id>/restaurar', methods=['GET', 'POST'])
@admin_required
def backup_restaurar(id):
    rec = BackupRecord.query.get_or_404(id)
    if request.method == 'POST':
        if request.form.get('confirmacao', '').strip().upper() != 'RESTAURAR':
            flash('Digite exatamente "RESTAURAR" (em maiúsculas) para confirmar.', 'danger')
            return redirect(url_for('backup_restaurar', id=id))
        if not rec.conteudo:
            flash('Esse backup não tem mais o arquivo disponível.', 'danger')
            return redirect(url_for('backup_lista'))
        try:
            zf = zipfile.ZipFile(io.BytesIO(rec.conteudo))
            dados = json.loads(zf.read('dados.json'))
        except Exception as e:
            flash(f'Backup corrompido ou inválido: {e}', 'danger')
            return redirect(url_for('backup_lista'))
        seguranca, erro = _executar_restauracao(dados)
        if erro:
            flash(f'Erro ao restaurar — nada foi alterado. Detalhe: {erro}', 'danger')
            return redirect(url_for('backup_lista'))
        log_action(session['user_id'], session['username'], 'restaurar_backup', 'backup', rec.id,
                   f'Restaurado a partir do backup #{rec.id}; backup de segurança criado: #{seguranca.id}')
        flash(f'Dados restaurados a partir do backup de {rec.created_at.strftime("%d/%m/%Y %H:%M")}! '
              f'(o estado anterior foi salvo no backup #{seguranca.id}, caso precise desfazer)', 'success')
        return redirect(url_for('dashboard'))
    return render_template('backup_restaurar.html', rec=rec, upload=False)

@app.route('/backup/restaurar-upload', methods=['GET', 'POST'])
@admin_required
def backup_restaurar_upload():
    if request.method == 'POST':
        if request.form.get('confirmacao', '').strip().upper() != 'RESTAURAR':
            flash('Digite exatamente "RESTAURAR" (em maiúsculas) para confirmar.', 'danger')
            return redirect(url_for('backup_restaurar_upload'))
        arquivo = request.files.get('arquivo')
        if not arquivo or not arquivo.filename:
            flash('Selecione um arquivo de backup (.zip) para enviar.', 'danger')
            return redirect(url_for('backup_restaurar_upload'))
        try:
            conteudo = arquivo.read()
            zf = zipfile.ZipFile(io.BytesIO(conteudo))
            dados = json.loads(zf.read('dados.json'))
        except Exception as e:
            flash(f'Arquivo inválido — precisa ser um .zip gerado por este sistema. Detalhe: {e}', 'danger')
            return redirect(url_for('backup_restaurar_upload'))
        seguranca, erro = _executar_restauracao(dados)
        if erro:
            flash(f'Erro ao restaurar — nada foi alterado. Detalhe: {erro}', 'danger')
            return redirect(url_for('backup_restaurar_upload'))
        log_action(session['user_id'], session['username'], 'restaurar_backup_upload', 'backup', None,
                   f'Restaurado a partir de arquivo enviado; backup de segurança criado: #{seguranca.id}')
        flash(f'Dados restaurados a partir do arquivo enviado! '
              f'(o estado anterior foi salvo no backup #{seguranca.id}, caso precise desfazer)', 'success')
        return redirect(url_for('dashboard'))
    return render_template('backup_restaurar.html', rec=None, upload=True)

_NOMES_FICTICIOS_CURSO = [
    'Curso Demonstrativo', 'Formação Exemplo', 'Capacitação Modelo',
    'Programa Ilustrativo', 'Trilha de Estudo Fictícia', 'Especialização Exemplo',
]
_NOMES_FICTICIOS_DISCIPLINA = [
    'Disciplina Introdutória', 'Fundamentos do Tema', 'Módulo Prático',
    'Tópicos Avançados', 'Estudo de Caso', 'Revisão Aplicada',
]
_NOMES_FICTICIOS_PESSOA = [
    'Ana Exemplo', 'Bruno Modelo', 'Carla Fictícia', 'Diego Amostra',
    'Elisa Teste', 'Fábio Ilustrativo', 'Gabriela Demo', 'Hugo Simulado',
]

def _mapa_nomes_ficticios():
    """Mapa estável nome-real (da equipe atual) -> nome-fictício, sempre na
    mesma ordem (alfabética, via responsaveis_atuais()) — usado tanto pra
    gerar os dados fictícios quanto pra exibir insersor/responsável pra
    conta de demonstração, pra ficar tudo consistente entre si."""
    equipe = responsaveis_atuais()
    return {_norm_name(nome): _NOMES_FICTICIOS_PESSOA[i % len(_NOMES_FICTICIOS_PESSOA)]
            for i, nome in enumerate(equipe)}

def _gerar_dados_ficticios():
    """Troca nome de curso/disciplina/professor/insersor/aluno/parceiro por
    dado fictício — nunca mexe em número (valor, horas, datas, ids) nem em
    conta de usuário (login quebraria). Usa o mapa estável da equipe, então
    o mesmo nome real sempre vira o mesmo fictício — e bate com o que a
    conta de demonstração vê no filtro de insersor do dashboard."""
    mapa_equipe = _mapa_nomes_ficticios()
    mapa_extras = {}
    def _fic_pessoa(nome_real):
        if not nome_real:
            return nome_real
        partes = [p.strip() for p in nome_real.split(',') if p.strip()]
        ficticias = []
        for p in partes:
            p_norm = _norm_name(p)
            if len(p) == 1:
                p_norm = _norm_name(INICIAIS_INSERCAO.get(p.upper(), p))
            if p_norm in mapa_equipe:
                ficticias.append(mapa_equipe[p_norm])
            else:
                if p_norm not in mapa_extras:
                    mapa_extras[p_norm] = f'Colaborador Externo {len(mapa_extras) + 1}'
                ficticias.append(mapa_extras[p_norm])
        return ', '.join(ficticias)

    cursos = Course.query.order_by(Course.id).all()
    for i, c in enumerate(cursos):
        c.nome = f'{_NOMES_FICTICIOS_CURSO[i % len(_NOMES_FICTICIOS_CURSO)]} {i + 1:03d}'
        if c.dono: c.dono = _fic_pessoa(c.dono)
        if c.insersor: c.insersor = _fic_pessoa(c.insersor)
        if c.obs: c.obs = 'Observação fictícia de demonstração.'
        if c.descricao: c.descricao = 'Descrição fictícia de demonstração — texto de exemplo.'
        if c.link_venda: c.link_venda = 'https://exemplo.com/curso-demo'

    discs = Discipline.query.order_by(Discipline.id).all()
    for i, d in enumerate(discs):
        d.nome = f'{_NOMES_FICTICIOS_DISCIPLINA[i % len(_NOMES_FICTICIOS_DISCIPLINA)]} {i + 1:03d}'
        if d.professor: d.professor = _fic_pessoa(d.professor)

    refunds = Refund.query.order_by(Refund.id).all()
    for i, r in enumerate(refunds):
        r.nome_aluno = f'Aluno Fictício {i + 1:03d}'
        r.nome_curso = f'Curso Fictício {i + 1:03d}'
        if r.colab: r.colab = _fic_pessoa(r.colab)
        if r.cpf: r.cpf = '000.000.000-00'
        if r.celular: r.celular = '(00) 00000-0000'
        if r.pix: r.pix = 'pix-demo@exemplo.com'
        if r.email_destino: r.email_destino = 'aluno.demo@exemplo.com'
        if r.motivo: r.motivo = 'Motivo fictício de demonstração.'
        if r.obs: r.obs = 'Observação fictícia.'

    terceiros = ThirdPartyPayment.query.order_by(ThirdPartyPayment.id).all()
    for i, t in enumerate(terceiros):
        t.terceiro = f'Parceiro Fictício {i + 1:03d}'

    setting = AppSetting.query.get('dados_ficticios_ativos')
    if not setting:
        setting = AppSetting(key='dados_ficticios_ativos')
        db.session.add(setting)
    setting.value = '1'

    db.session.commit()
    return {'cursos': len(cursos), 'disciplinas': len(discs),
            'reembolsos': len(refunds), 'terceiros': len(terceiros)}

def _dados_ficticios_ativos():
    setting = AppSetting.query.get('dados_ficticios_ativos')
    return bool(setting and setting.value == '1')

@app.route('/admin/gerar-dados-ficticios', methods=['GET', 'POST'])
@admin_required
def admin_gerar_dados_ficticios():
    """Ação irreversível pensada só pro ambiente de demonstração/teste —
    troca nome real por fictício em todo o banco. Exige confirmação digitada
    e mostra o host do banco de dados atual, igual à restauração de backup,
    pra reduzir ao máximo o risco de rodar isso sem querer na produção."""
    if request.method == 'POST':
        if request.form.get('confirmacao', '').strip().upper() != 'FICTICIO':
            flash('Digite exatamente "FICTICIO" (em maiúsculas) para confirmar.', 'danger')
            return redirect(url_for('admin_gerar_dados_ficticios'))
        resumo = _gerar_dados_ficticios()
        log_action(session['user_id'], session['username'], 'gerar_dados_ficticios', 'sistema', None,
                   f"Cursos={resumo['cursos']}, Disciplinas={resumo['disciplinas']}, "
                   f"Reembolsos={resumo['reembolsos']}, Terceiros={resumo['terceiros']}")
        flash('Dados fictícios gerados! Números e contas de usuário continuam iguais.', 'success')
        return redirect(url_for('dashboard'))
    host_match = _re.search(r'@([^/]+)/', _db_url)
    db_host = host_match.group(1) if host_match else _db_url
    contas_demo = [u for u in User.query.order_by(User.username).all() if u.is_conta_demo()]
    return render_template('admin_gerar_dados_ficticios.html', db_host=db_host,
                           contas_demo=contas_demo, demo_publico_user_id=_demo_publico_user_id())

@app.route('/admin/demonstracao-config', methods=['POST'])
@admin_required
def admin_demonstracao_config():
    """Escolhe (ou desliga) qual conta o link público /demonstracao usa —
    sempre uma decisão explícita do admin, nunca detectada sozinha."""
    uid = request.form.get('user_id', '').strip()
    setting = AppSetting.query.get('demo_publico_user_id')
    if not setting:
        setting = AppSetting(key='demo_publico_user_id')
        db.session.add(setting)
    if uid:
        conta = User.query.get(int(uid))
        if not conta or not conta.is_conta_demo():
            flash('Escolha uma conta que esteja marcada como "Conta de demonstração".', 'danger')
            return redirect(url_for('admin_gerar_dados_ficticios'))
        setting.value = str(conta.id)
        db.session.commit()
        log_action(session['user_id'], session['username'], 'ativar_demonstracao', 'sistema', None,
                   f'Link /demonstracao ligado, usando a conta "{conta.username}"')
        flash(f'Link público de demonstração ativado, usando a conta "{conta.username}".', 'success')
    else:
        setting.value = None
        db.session.commit()
        log_action(session['user_id'], session['username'], 'desativar_demonstracao', 'sistema', None)
        flash('Link público de demonstração desativado.', 'success')
    return redirect(url_for('admin_gerar_dados_ficticios'))

def arquivar_logs_antigos():
    """Arquiva por e-mail e remove da tabela ativa os logs de auditoria com mais
    de 1 mês — não perde o histórico (ele continua tanto no e-mail de arquivo
    quanto dentro dos backups diários completos), só tira da tabela usada no
    dia a dia para o sistema não ficar sobrecarregado."""
    limite = datetime.utcnow() - timedelta(days=30)
    antigos = AuditLog.query.filter(AuditLog.timestamp < limite).all()
    if not antigos:
        return 0
    dados = [{col.name: _serializar_valor(getattr(a, col.name)) for col in AuditLog.__table__.columns}
             for a in antigos]
    json_bytes = json.dumps(dados, ensure_ascii=False, default=str).encode('utf-8')
    ts = datetime.now().strftime('%Y%m%d_%H%M%S')
    fname = f'logs_arquivados_{ts}.zip'
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, 'w', zipfile.ZIP_DEFLATED) as zf:
        zf.writestr('logs_arquivados.json', json_bytes)
    conteudo = buf.getvalue()

    destino = os.environ.get('EMAIL_BACKUP_DESTINO', EMAIL_SMTP_USER)
    if destino:
        enviar_email_com_anexo(
            destino,
            f'Logs arquivados — Gestor Acadêmico — {ts}',
            f'{len(antigos)} registro(s) de histórico com mais de 1 mês foram arquivados e removidos '
            'da tabela ativa para não sobrecarregar o sistema. O anexo contém todos eles em JSON — '
            'e eles também continuam preservados nos backups diários completos.',
            conteudo, fname,
        )

    qtd = len(antigos)
    for a in antigos:
        db.session.delete(a)
    db.session.commit()
    return qtd

@app.route('/admin/video-presets', methods=['GET', 'POST'])
@perm_check('can_manage_opcoes_curso')
def video_presets():
    if request.method == 'POST':
        if request.form.get('form_tipo') == 'venda_modalidade':
            label = request.form.get('venda_label', '').strip()
            if label:
                maior_ordem = db.session.query(db.func.max(VendaModalidadeOpcao.ordem)).scalar() or 0
                db.session.add(VendaModalidadeOpcao(label=label, ordem=maior_ordem + 1))
                db.session.commit()
                flash('Opção de "Venda por" adicionada!', 'success')
            else:
                flash('Preencha o nome da opção.', 'danger')
        else:
            label = request.form.get('label', '').strip()
            url = request.form.get('url', '').strip()
            if label and url:
                maior_ordem = db.session.query(db.func.max(VideoPreset.ordem)).scalar() or 0
                db.session.add(VideoPreset(label=label, url=url, ordem=maior_ordem + 1))
                db.session.commit()
                flash('Link de vídeo adicionado!', 'success')
            else:
                flash('Preencha a descrição e o link.', 'danger')
        return redirect(url_for('video_presets'))
    presets = VideoPreset.query.order_by(VideoPreset.ordem).all()
    venda_opcoes = VendaModalidadeOpcao.query.order_by(VendaModalidadeOpcao.ordem).all()
    return render_template('video_presets.html', presets=presets, venda_opcoes=venda_opcoes)

@app.route('/admin/video-presets/<int:id>/excluir', methods=['POST'])
@perm_check('can_manage_opcoes_curso')
def video_preset_excluir(id):
    p = VideoPreset.query.get_or_404(id)
    db.session.delete(p)
    db.session.commit()
    flash('Link de vídeo removido.', 'success')
    return redirect(url_for('video_presets'))

@app.route('/admin/venda-modalidades/<int:id>/excluir', methods=['POST'])
@perm_check('can_manage_opcoes_curso')
def venda_modalidade_excluir(id):
    o = VendaModalidadeOpcao.query.get_or_404(id)
    db.session.delete(o)
    db.session.commit()
    flash('Opção de "Venda por" removida.', 'success')
    return redirect(url_for('video_presets'))

# ─── FERRAMENTAS EXTERNAS (sistemas embutidos via iframe) ──────────────────────
# Ex: Kronos. Alguns sites bloqueiam ser exibidos em iframe (cabeçalho
# X-Frame-Options / Content-Security-Policy: frame-ancestors) — isso é uma
# proteção do próprio site contra clickjacking e não tem como ser contornada
# por aqui; nesses casos a tela mostra um aviso com link pra abrir em nova aba.
# A verificação é feita pelo SERVIDOR (olhando o cabeçalho de verdade que o
# site manda) — não dá pra confiar em "esperar um tempo e ver se carregou"
# no navegador, porque isso dá falso positivo em sites só um pouco lentos.

def _verifica_embeddable(url):
    """Confere se um site permite ser exibido em iframe, olhando os
    cabeçalhos X-Frame-Options e Content-Security-Policy da resposta.
    Retorna True (permite), False (bloqueia) ou None (não deu pra checar —
    site fora do ar, timeout etc; nesse caso tentamos o iframe mesmo assim)."""
    try:
        r = _requests.get(url, timeout=6, allow_redirects=True,
                           headers={'User-Agent': 'Mozilla/5.0 (compatible; GestorAcademico/1.0)'})
    except _requests.RequestException:
        return None
    xfo = (r.headers.get('X-Frame-Options') or '').strip().upper()
    if xfo in ('DENY', 'SAMEORIGIN'):
        return False
    csp = r.headers.get('Content-Security-Policy') or ''
    for diretiva in csp.split(';'):
        diretiva = diretiva.strip()
        if diretiva.lower().startswith('frame-ancestors'):
            valor = diretiva[len('frame-ancestors'):].strip()
            if valor and '*' not in valor:
                return False
    return True

@app.route('/ferramentas')
@perm_check('can_view_ferramentas')
def ferramentas():
    tools = ExternalTool.query.order_by(ExternalTool.ordem, ExternalTool.label).all()
    return render_template('ferramentas.html', tools=tools)

@app.route('/ferramentas/nova', methods=['POST'])
@admin_required
def ferramenta_nova():
    label = request.form.get('label', '').strip()
    url = request.form.get('url', '').strip()
    if label and url:
        maior_ordem = db.session.query(db.func.max(ExternalTool.ordem)).scalar() or 0
        db.session.add(ExternalTool(label=label, url=url, ordem=maior_ordem + 1))
        db.session.commit()
        flash('Ferramenta adicionada!', 'success')
    else:
        flash('Preencha o nome e o link.', 'danger')
    return redirect(url_for('ferramentas'))

@app.route('/ferramentas/<int:id>/editar', methods=['POST'])
@admin_required
def ferramenta_editar(id):
    t = ExternalTool.query.get_or_404(id)
    label = request.form.get('label', '').strip()
    url = request.form.get('url', '').strip()
    if label and url:
        t.label = label
        t.url = url
        db.session.commit()
        flash('Ferramenta atualizada!', 'success')
    else:
        flash('Preencha o nome e o link.', 'danger')
    return redirect(url_for('ferramentas'))

@app.route('/ferramentas/<int:id>/excluir', methods=['POST'])
@admin_required
def ferramenta_excluir(id):
    t = ExternalTool.query.get_or_404(id)
    db.session.delete(t)
    db.session.commit()
    flash('Ferramenta removida.', 'success')
    return redirect(url_for('ferramentas'))

@app.route('/ferramentas/<int:id>/revalidar', methods=['POST'])
@admin_required
def ferramenta_revalidar(id):
    """Força reconferir agora se o site permite iframe, sem esperar o
    cache de 1 dia — útil logo depois de mudar a config do lado de lá."""
    t = ExternalTool.query.get_or_404(id)
    t.embeddable = _verifica_embeddable(t.url)
    t.embeddable_checado_em = datetime.utcnow()
    db.session.commit()
    if t.embeddable:
        flash(f'"{t.label}" agora permite ser aberto aqui dentro!', 'success')
    else:
        flash(f'"{t.label}" ainda bloqueia — confira se a mudança já foi publicada do lado de lá.', 'danger')
    return redirect(url_for('ferramentas'))

@app.route('/ferramentas/<int:id>/abrir')
@perm_check('can_view_ferramentas')
def ferramenta_abrir(id):
    t = ExternalTool.query.get_or_404(id)
    # Recheca de tempos em tempos (1 dia) — o site pode mudar de política.
    precisa_checar = (t.embeddable_checado_em is None or
                       datetime.utcnow() - t.embeddable_checado_em > timedelta(days=1))
    if precisa_checar:
        t.embeddable = _verifica_embeddable(t.url)
        t.embeddable_checado_em = datetime.utcnow()
        db.session.commit()
    return render_template('ferramenta_abrir.html', tool=t)

_MODULOS_ORDEM_IDS = {m['id'] for m in MODULOS_CATALOGO}

@app.route('/api/modulos-ordem', methods=['POST'])
@admin_required
def api_modulos_ordem():
    """Só admin mexe na ordem dos itens/subcategorias dentro das seções do
    menu (ex: Cursos/Cupons/Reembolsos/... dentro de INOVA CARREIRA) — vale
    globalmente pra todo mundo, igual a ordem das seções. Só reordena; quem
    enxerga cada item continua sendo decidido pela permissão/visibilidade
    de cada um."""
    data = request.get_json(silent=True) or {}
    ordem = data.get('order', [])
    if not isinstance(ordem, list):
        return jsonify({'ok': False, 'erro': 'Formato inválido.'}), 400
    ordem = [s for s in ordem if s in _MODULOS_ORDEM_IDS]
    setting = AppSetting.query.get('modulos_ordem')
    if not setting:
        setting = AppSetting(key='modulos_ordem')
        db.session.add(setting)
    setting.value = json.dumps(ordem) if ordem else None
    db.session.commit()
    return jsonify({'ok': True})

@app.route('/api/ferramentas-ordem', methods=['POST'])
@admin_required
def api_ferramentas_ordem():
    """Só admin mexe na ordem das ferramentas externas no menu — grava
    direto no campo `ordem` de cada uma (mesmo campo já usado quando uma
    ferramenta nova é cadastrada), vale globalmente pra todo mundo."""
    data = request.get_json(silent=True) or {}
    ordem = data.get('order', [])
    if not isinstance(ordem, list):
        return jsonify({'ok': False, 'erro': 'Formato inválido.'}), 400
    try:
        ids = [int(i) for i in ordem]
    except (TypeError, ValueError):
        return jsonify({'ok': False, 'erro': 'Formato inválido.'}), 400
    tools = {t.id: t for t in ExternalTool.query.filter(ExternalTool.id.in_(ids)).all()}
    for posicao, tool_id in enumerate(ids):
        if tool_id in tools:
            tools[tool_id].ordem = posicao
    db.session.commit()
    return jsonify({'ok': True})

SIDEBAR_SECOES_VALIDAS = {'inova_carreira', 'ferramentas', 'erp_moodle', 'gestao', 'admin'}

@app.route('/api/sidebar-ordem', methods=['POST'])
@admin_required
def api_sidebar_ordem():
    """Só admin mexe na ordem das seções do menu lateral — vale globalmente
    pra todo mundo que loga, igual as permissões que o admin já controla."""
    data = request.get_json(silent=True) or {}
    ordem = data.get('order', [])
    if not isinstance(ordem, list):
        return jsonify({'ok': False, 'erro': 'Formato inválido.'}), 400
    ordem = [s for s in ordem if s in SIDEBAR_SECOES_VALIDAS]
    setting = AppSetting.query.get('sidebar_section_order')
    if not setting:
        setting = AppSetting(key='sidebar_section_order')
        db.session.add(setting)
    setting.value = json.dumps(ordem) if ordem else None
    db.session.commit()
    return jsonify({'ok': True})

@app.route('/api/eventos/pendentes-ocultar')
@login_required
def api_eventos_pendentes_ocultar():
    """Consultado via JS (a cada 30 min) pra disparar a notificação do
    navegador lembrando de ocultar eventos que já terminaram/terminam amanhã."""
    u = User.query.get(session['user_id'])
    if not u or u.role not in ('admin', 'editor'):
        return jsonify({'eventos': []})
    hoje = date.today()
    eventos = _eventos_pendentes_ocultar()
    return jsonify({'eventos': [
        {
            'id': e.id, 'nome': e.nome,
            'data_finalizacao': e.data_finalizacao.isoformat(),
            'vencido': e.data_finalizacao <= hoje,
            'url': url_for('curso_editar', id=e.id),
        }
        for e in eventos
    ]})

def _enviar_avisos_whatsapp_pendentes():
    """Roda uma vez por dia (junto do cron de backup, ver cron_backup):
    manda WhatsApp pra quem optou em cada lembrete/aviso — só uma vez por
    ocorrência/disparo, mesmo rodando todo dia (ver ultimo_whatsapp_ocorrencia
    e alerta_whatsapp_enviado). Nunca deixa a falta de telefone/apikey do
    CallMeBot quebrar o cron (enviar_whatsapp já é à prova disso)."""
    enviados_lembretes = 0
    for l in LembreteFixo.query.filter_by(ativo=True, avisar_whatsapp=True).all():
        pend = _lembrete_pendencia(l)
        if not pend or l.ultimo_whatsapp_ocorrencia == pend['ocorrencia']:
            continue
        dono = User.query.get(l.user_id)
        if dono and dono.telefone_whatsapp and dono.whatsapp_apikey:
            label = {'hoje': 'hoje', 'amanha': 'amanhã'}.get(pend['status'], f"atrasado {pend['dias_atraso']} dia(s)")
            if enviar_whatsapp(dono.telefone_whatsapp, dono.whatsapp_apikey,
                                f'⏰ Lembrete do Gestor Acadêmico — {label}: {l.titulo}'):
                enviados_lembretes += 1
        l.ultimo_whatsapp_ocorrencia = pend['ocorrencia']
    db.session.commit()

    enviados_demandas = 0
    for d in Demanda.query.filter_by(alerta_ativo=True, alerta_whatsapp=True, alerta_whatsapp_enviado=False).all():
        for u in d.responsaveis_usuarios():
            if u.telefone_whatsapp and u.whatsapp_apikey:
                texto = f'🔔 Aviso da equipe (Gestor Acadêmico) — {d.titulo}: {d.alerta_texto or "confira a demanda no Calendário."}'
                if enviar_whatsapp(u.telefone_whatsapp, u.whatsapp_apikey, texto):
                    enviados_demandas += 1
        d.alerta_whatsapp_enviado = True
    db.session.commit()

    resumo = _resumo_diario_sino()
    if resumo:
        _notificar_admins_whatsapp('sino_diario', resumo)

    return {'lembretes': enviados_lembretes, 'demandas': enviados_demandas}

@app.route('/cron/backup')
def cron_backup():
    """Chamada automaticamente pelo Vercel Cron (veja vercel.json). Como o
    ambiente serverless não mantém processos rodando o tempo todo, o backup
    diário e o arquivamento de logs precisam de um gatilho externo como esse,
    em vez da thread usada quando roda local (backup_scheduler). Rodar todo
    dia também mantém o projeto Supabase "ativo", evitando a pausa automática
    por inatividade do plano gratuito. Aproveita a mesma chamada diária pra
    também mandar os avisos de WhatsApp pendentes (ver _enviar_avisos_whatsapp_pendentes)."""
    secret = os.environ.get('CRON_SECRET')
    if secret and request.headers.get('Authorization') != f'Bearer {secret}':
        return 'Não autorizado', 401
    rec = make_backup(tipo='auto')
    qtd_arquivados = arquivar_logs_antigos()
    try:
        whatsapp_enviados = _enviar_avisos_whatsapp_pendentes()
    except Exception as e:
        print(f'[ERRO CRON WHATSAPP] {e}')
        whatsapp_enviados = None
    return jsonify({'backup_id': rec.id, 'tamanho_kb': rec.size_kb, 'logs_arquivados': qtd_arquivados,
                     'whatsapp_enviados': whatsapp_enviados})

# ─── SEED DATA ─────────────────────────────────────────────────────────────────

def _import_excel():
    import re as _re2

    def is_numero(val):
        try: return int(str(val).strip()) > 0
        except: return False

    def limpar_horas(val):
        if val is None: return ''
        m = _re2.match(r'^(\d+\.?\d*)', str(val).strip())
        return m.group(1) if m else ''

    def limpar_valor(val):
        if val is None: return ''
        s = str(val).strip()
        return s if s not in ('-', '') else ''

    def pd(v):
        return v.date() if isinstance(v, datetime) else None

    admin = User.query.filter_by(username='admin').first()
    admin_id = admin.id if admin else None

    def ac(nome, tipo, area, horas, valor, link, link_img='', desc='', obs='', status='ativo', insersor='', meses='', cupom='', dono=''):
        if not nome or str(nome).strip() == '': return None
        c = Course(nome=str(nome).strip()[:300], tipo=tipo,
                   area=str(area or '').strip()[:100], horas=str(horas or '').strip()[:20],
                   meses=str(meses or '').strip()[:20], valor=str(valor or '').strip()[:50],
                   link_venda=str(link or '').strip(), link_imagem=str(link_img or '').strip(),
                   descricao=str(desc or '').strip(), obs=str(obs or '').strip(),
                   status=status, insersor=str(insersor or '').strip()[:100],
                   cupom=str(cupom or '').strip()[:100], dono=str(dono or '').strip(),
                   created_by=admin_id)
        db.session.add(c)
        return c

    try:
        import openpyxl
        excel_path = os.path.join(os.path.dirname(__file__), 'CURSOS INOVA - LINKS (1).xlsx')
        wb = openpyxl.load_workbook(excel_path)

        # PÓS-GRADUAÇÃO — só linhas onde col[0] é número (ignora linhas de disciplinas)
        for shname in wb.sheetnames:
            if 'MATRIZES' in shname.upper():
                ws = wb[shname]
                for row in ws.iter_rows(min_row=3, values_only=True):
                    if not is_numero(row[0]): continue
                    area_val = str(row[2] or '').strip()
                    if area_val.endswith('h') and area_val[:-1].isdigit(): continue
                    ac(row[1], 'pos', row[2], limpar_horas(row[3]), limpar_valor(row[5]),
                       str(row[7] or ''), obs=str(row[8] or ''), insersor=str(row[6] or ''),
                       meses=str(row[4] or ''))
                break

        # PROFISSIONALIZANTES
        for shname in wb.sheetnames:
            if 'PROFISSIONALIZANTE' in shname.upper():
                ws = wb[shname]
                for row in ws.iter_rows(min_row=2, values_only=True):
                    if not is_numero(row[0]): continue
                    ac(row[1], 'profissionalizante', row[2], limpar_horas(row[3]), '',
                       str(row[4] or ''), link_img=str(row[6] or ''),
                       desc=str(row[5] or ''), obs=str(row[7] or ''), insersor='INOVA')
                break

        # RÁPIDOS
        for shname in wb.sheetnames:
            if 'RÁPIDOS INOVA' in shname or 'RAPIDOS INOVA' in shname:
                ws = wb[shname]
                for row in ws.iter_rows(min_row=2, values_only=True):
                    if not is_numero(row[0]): continue
                    ac(row[1], 'rapido', row[2], limpar_horas(row[3]), limpar_valor(row[5]),
                       str(row[4] or ''), link_img=str(row[7] or ''),
                       desc=str(row[6] or ''), obs=str(row[8] or ''), insersor='INOVA')
                break

        # PACOTES
        for shname in wb.sheetnames:
            if shname.upper() == 'PACOTE CURSOS':
                ws = wb[shname]
                for row in ws.iter_rows(min_row=2, values_only=True):
                    if not is_numero(row[0]): continue
                    ac(row[1], 'pacote', row[2], limpar_horas(row[3]), limpar_valor(row[8]),
                       str(row[4] or ''), obs=str(row[6] or ''), insersor=str(row[5] or ''))
                break

        # TERCEIROS
        for shname in wb.sheetnames:
            if 'TERCEIROS' in shname.upper():
                ws = wb[shname]
                for row in ws.iter_rows(min_row=2, values_only=True):
                    if not is_numero(row[0]): continue
                    obs = str(row[10] or '').strip()
                    s = 'descontinuado' if 'DESCONTINUADO' in obs.upper() else 'ativo'
                    ac(row[1], 'terceiros', row[5], limpar_horas(row[3]), limpar_valor(row[2]),
                       str(row[6] or ''), desc=str(row[8] or ''), obs=obs, dono=str(row[7] or ''))
                break

        # EVENTOS
        for shname in wb.sheetnames:
            if shname.upper() == 'EVENTOS':
                ws = wb[shname]
                for row in ws.iter_rows(min_row=2, values_only=True):
                    if not row[2]: continue
                    obs_ev = f"Tipo: {row[1] or ''} | Data: {row[5] or ''}" + (f" | {row[8]}" if row[8] else "")
                    ac(row[2], 'evento', 'EVENTO', limpar_horas(row[3]), limpar_valor(row[6]),
                       str(row[4] or ''), obs=obs_ev, insersor='INOVA')
                break

        # PRÁTICAS CONECTADAS
        for shname in wb.sheetnames:
            if 'CONECTADA' in shname.upper():
                ws = wb[shname]
                for row in ws.iter_rows(min_row=2, values_only=True):
                    if not row[1]: continue
                    ac(row[1], 'pratica_conectada', str(row[0] or ''), '', '',
                       str(row[3] or ''), status='oculto', insersor='INOVA', cupom=str(row[2] or ''))
                break

        # PRÁTICAS ESTÁGIO
        for shname in wb.sheetnames:
            if 'ESTAGIO' in shname.upper() or 'ESTÁGIO' in shname.upper():
                ws = wb[shname]
                for row in ws.iter_rows(min_row=2, values_only=True):
                    if not row[0]: continue
                    ac(row[0], 'pratica_estagio', str(row[1] or ''), '', '',
                       str(row[5] or ''), insersor=str(row[3] or ''), cupom=str(row[4] or ''))
                break

        # PROJ. AMBIENTES PROF
        for shname in wb.sheetnames:
            if 'AMBIENTES' in shname.upper():
                ws = wb[shname]
                for row in ws.iter_rows(min_row=2, values_only=True):
                    if not is_numero(row[0]): continue
                    ac(row[1], 'projeto_ambiental', '', '', '', str(row[3] or ''),
                       status='oculto', insersor='INOVA', cupom=str(row[2] or ''), obs=str(row[4] or ''))
                break

        # GGBR
        for shname in wb.sheetnames:
            if 'GGBR' in shname.upper():
                ws = wb[shname]
                for row in ws.iter_rows(min_row=2, values_only=True):
                    if not is_numero(row[0]): continue
                    ac(row[1], 'ggbr', str(row[2] or ''), limpar_horas(row[3]),
                       limpar_valor(row[5]), str(row[4] or ''), insersor='INOVA')
                break

        # INTEGRA EDU
        for shname in wb.sheetnames:
            if 'INTEGRA' in shname.upper():
                ws = wb[shname]
                for row in ws.iter_rows(min_row=2, values_only=True):
                    if not row[0]: continue
                    ac(row[0], 'integra_edu', '', limpar_horas(row[1]), '',
                       str(row[2] or ''), obs=str(row[3] or ''), insersor='INOVA')
                break

        db.session.commit()

        # CUPONS — só importa se não há cupons ainda
        if Coupon.query.count() == 0:
            for shname in wb.sheetnames:
                if shname.upper() == 'CUPOM':
                    ws = wb[shname]
                    for row in ws.iter_rows(min_row=2, values_only=True):
                        if not row[0] or str(row[0]).strip() in ('NOME', ''): continue
                        try:
                            cp = Coupon(nome=str(row[0]).strip()[:100], quantidade=int(row[1] or 0),
                                       desconto=float(row[2] or 0), cursos_tipo=str(row[3] or '').strip(),
                                       limite_curso=int(row[4] or 1), uso_unico=(str(row[5] or '').upper()=='SIM'),
                                       data_inicial=pd(row[6]), data_final=pd(row[7]) if len(row) > 7 else None,
                                       obs=str(row[8] or '').strip() if len(row) > 8 else '')
                            db.session.add(cp)
                        except: pass
                    break

        # REEMBOLSOS — só importa se não há reembolsos ainda
        if Refund.query.count() == 0:
            for shname in wb.sheetnames:
                if 'REEMBOLSO' in shname.upper():
                    ws = wb[shname]
                    for row in ws.iter_rows(min_row=2, values_only=True):
                        if not row[1] or str(row[1]).strip() in ('NOME ALUNO', ''): continue
                        try:
                            r = Refund(colab=str(row[0] or '').strip(), nome_aluno=str(row[1] or '').strip(),
                                      data_compra=pd(row[2]), data_solicitacao=pd(row[3]),
                                      valor=float(str(row[4] or 0).replace(',', '.') or 0),
                                      valor_estorno=float(str(row[5] or 0).replace(',', '.') or 0),
                                      nome_curso=str(row[6] or '').strip(), categoria=str(row[7] or '').strip(),
                                      data_aprovacao=pd(row[10]) if len(row) > 10 else None,
                                      motivo=str(row[11] or '').strip() if len(row) > 11 else '')
                            db.session.add(r)
                        except: pass
                    break

        db.session.commit()

        # ── DISCIPLINAS DAS MATRIZES (PÓS) ────────────────────────────────
        import unicodedata as _ud

        def norm_nome(s):
            s = _re2.sub(r'\s+', ' ', str(s).upper().strip())
            s = ''.join(c for c in _ud.normalize('NFKD', s) if not _ud.combining(c))
            return _re2.sub(r'\s+', ' ', s).strip()

        def norm_compact(s):
            return _re2.sub(r'\s+', '', norm_nome(s))

        def nome_sim(a, b):
            na, nb = norm_nome(a), norm_nome(b)
            if na == nb:
                return True
            # Compara sem espaços (resolve \xa0 embutido)
            ca, cb = norm_compact(a), norm_compact(b)
            if ca == cb:
                return True
            # Prefixo longo (evita colisão entre "EDUCACAO DO FUTURO" e "EDUCACAO INTEGRADA...")
            for n in [55, 50, 45, 40]:
                if len(ca) >= n and len(cb) >= n and ca[:n] == cb[:n]:
                    return True
            # Prefixo com espaços (normalizado) — só acima de 35 chars
            for n in [45, 40, 35]:
                if len(na) >= n and len(nb) >= n and na[:n] == nb[:n]:
                    return True
            return False

        pos_courses = Course.query.filter_by(tipo='pos').all()

        sheet_m = next((s for s in wb.sheetnames if 'MATRIZES' in s.upper()), None)
        if sheet_m and pos_courses:
            ws_m = wb[sheet_m]
            all_rows = list(ws_m.iter_rows(min_row=3, values_only=True))

            # Encontrar onde terminam as linhas de cursos e começam as matrizes
            matrix_start = len(all_rows)
            for i, row in enumerate(all_rows):
                try: int(str(row[0] or '').strip())
                except:
                    matrix_start = i
                    break

            cur_id = None
            in_disc = False
            disc_ordem = 0
            cur_modulo = None

            for row in all_rows[matrix_start:]:
                c0 = str(row[0] or '').strip()
                c1 = str(row[1] or '').strip()
                c2 = str(row[2] or '').strip()
                c3 = str(row[3] or '').strip()

                if not c0 and not c1 and not c2 and not c3:
                    in_disc = False
                    continue

                if c1.upper() == 'DISCIPLINAS':
                    in_disc = True
                    disc_ordem = 0
                    cur_modulo = None
                    continue

                if not c0 and not c1 and c2:
                    continue

                if not c2:
                    cname = c0 if (c0 and not c1) else c1
                    if cname and cname.upper() not in ('PROFESSOR', 'PROFESSORES', 'DISCIPLINAS'):
                        in_disc = False
                        disc_ordem = 0
                        cur_modulo = None
                        cur_id = None
                        match = next((c for c in pos_courses if nome_sim(c.nome, cname)), None)
                        if match:
                            existing = Discipline.query.filter_by(course_id=match.id).count()
                            cur_id = match.id if existing == 0 else None
                    continue

                if in_disc and c1 and c2 and cur_id:
                    if c0 and not c0.isdigit():
                        cur_modulo = c0
                        disc_ordem += 1
                    elif c0 and c0.isdigit():
                        disc_ordem = int(c0)
                    else:
                        disc_ordem += 1
                    db.session.add(Discipline(
                        course_id=cur_id, modulo=cur_modulo,
                        ordem=disc_ordem, nome=c1, carga=c2 or None,
                        professor=c3 or None
                    ))

            db.session.commit()

        # ── DISCIPLINAS DOS PROFISSIONALIZANTES ───────────────────────────
        # Layout: 2 matrizes lado a lado — mas os dois blocos NÃO ficam
        # sincronizados na mesma linha (um curso pode ter mais ou menos
        # disciplinas que o vizinho), então cada bloco é percorrido de forma
        # totalmente independente do outro (ver _parse_bloco_prof abaixo).
        # Bloco 1: C9=modulo/nome do curso, C10=ordem, C11=nome, C12=ch
        # Bloco 2: C14=modulo/nome do curso, C15=ordem, C16=nome, C17=ch
        # O nome do curso fica na linha ANTES do cabeçalho "DISCIPLINAS" do
        # próprio bloco.
        prof_courses = Course.query.filter_by(tipo='profissionalizante').all()
        sheet_prof = next((s for s in wb.sheetnames if 'PROFISSIONALIZANTE' in s.upper()), None)
        if sheet_prof and prof_courses:
            # Preposições que variam entre a lista de cursos e o bloco da
            # matriz sem mudar o curso (ex.: "ASSISTENTE PARA IMPLANTAÇÃO..."
            # vs "ASSISTENTE DE IMPLANTAÇÃO...") e a abreviação "IA" — são
            # ignoradas/unificadas só no último critério de correspondência,
            # depois que nome exato/prefixo já falharam.
            _STOPWORDS_PROF = {'DE','DA','DO','DAS','DOS','EM','NO','NA','NOS','NAS',
                                'PARA','COM','E','A','O','AO','AOS'}
            def _tokens_prof(s):
                palavras = _re2.sub(r'\bIA\b', 'INTELIGENCIA ARTIFICIAL', norm_nome(s)).split()
                return frozenset(w for w in palavras if w not in _STOPWORDS_PROF)

            prof_map = {}
            prof_map_compact = {}
            prof_map_semantico = {}
            for c in prof_courses:
                prof_map[norm_nome(c.nome)] = c
                prof_map_compact[norm_compact(c.nome)] = c
                prof_map_semantico[_tokens_prof(c.nome)] = c

            def _match_prof(nome_excel):
                key = norm_nome(nome_excel)
                if key in prof_map:
                    return prof_map[key]
                ck = norm_compact(nome_excel)
                if ck in prof_map_compact:
                    return prof_map_compact[ck]
                for n in [40, 35, 30, 25, 20]:
                    for k, c in prof_map_compact.items():
                        if len(ck) >= n and len(k) >= n and ck[:n] == k[:n]:
                            return c
                tok = _tokens_prof(nome_excel)
                if tok and tok in prof_map_semantico:
                    return prof_map_semantico[tok]
                return None

            def _cell(row, idx):
                return str(row[idx] or '').strip() if row and idx < len(row) else ''

            ws_p = wb[sheet_prof]
            rows_p = list(ws_p.iter_rows(min_row=1, values_only=True))

            def _parse_bloco_prof(idx_a, idx_ordem, idx_nome, idx_carga):
                cur_id = None
                pendente = None
                modulo = None
                for row in rows_p:
                    c_a = _cell(row, idx_a)
                    c_o = _cell(row, idx_ordem)
                    c_n = _cell(row, idx_nome)
                    c_c = _cell(row, idx_carga)

                    if c_n.upper() == 'DISCIPLINAS':
                        m = _match_prof(pendente) if pendente else None
                        cur_id = m.id if m and Discipline.query.filter_by(course_id=m.id).count() == 0 else None
                        modulo = None
                        pendente = None
                        continue

                    if c_a and not c_a.startswith('Mód') and not c_n:
                        pendente = c_a
                        continue

                    if c_a.startswith('Mód'):
                        modulo = c_a

                    if c_o.isdigit() and c_n and c_n.upper() not in ('DISCIPLINAS', 'CH') and cur_id:
                        db.session.add(Discipline(
                            course_id=cur_id, modulo=modulo,
                            ordem=int(c_o), nome=c_n, carga=c_c or None,
                            plataforma_ok=True, plataforma_em=datetime.utcnow()
                        ))

            _parse_bloco_prof(9, 10, 11, 12)    # Bloco 1
            _parse_bloco_prof(14, 15, 16, 17)   # Bloco 2

            db.session.commit()

        # ── MATRIZ DOS PACOTES ──────────────────────────────────────────────
        # Mesmo padrão usado em pós/profissionalizantes: 1 Discipline por item
        # do pacote. Fonte: aba "PACOTE CURSOS".
        # - Pacotes 5+: bloco lateral (colunas K:P a partir da lin. 41) — um
        #   cabeçalho (nome do pacote, com 'INSERSOR' na coluna M) seguido das
        #   disciplinas/cursos que o compõem.
        # - Pacotes 1-4: a lista vem em texto livre na coluna OBS (G), sem
        #   seguir o padrão do bloco lateral — curada manualmente abaixo.
        pacote_courses = Course.query.filter_by(tipo='pacote').all()
        sheet_pac = next((s for s in wb.sheetnames if s.strip().upper() == 'PACOTE CURSOS'), None)
        if sheet_pac and pacote_courses:
            pac_map = {}
            pac_map_compact = {}
            for c in pacote_courses:
                pac_map[norm_nome(c.nome)] = c
                pac_map_compact[norm_compact(c.nome)] = c

            def _match_pacote(nome_excel):
                key = norm_nome(nome_excel)
                if key in pac_map:
                    return pac_map[key]
                ck = norm_compact(nome_excel)
                if ck in pac_map_compact:
                    return pac_map_compact[ck]
                for n in [40, 35, 30, 25, 20]:
                    for k, c in pac_map_compact.items():
                        if len(ck) >= n and len(k) >= n and ck[:n] == k[:n]:
                            return c
                return None

            def _cellp(row, idx):
                return str(row[idx] or '').strip() if row and idx < len(row) else ''

            def _add_disc_concluida(course_id, ordem, nome, carga, professor=None):
                db.session.add(Discipline(
                    course_id=course_id, ordem=ordem, nome=nome, carga=carga or None,
                    professor=professor, plataforma_ok=True, plataforma_em=datetime.utcnow()
                ))

            ws_pac = wb[sheet_pac]
            rows_pac = list(ws_pac.iter_rows(min_row=1, values_only=True))
            cur_pac_id = None
            for row in rows_pac:
                c10 = _cellp(row, 10)  # nº
                c11 = _cellp(row, 11)  # nome (cabeçalho ou disciplina)
                c12 = _cellp(row, 12)  # 'INSERSOR' (cabeçalho) ou insersor real
                c14 = _cellp(row, 14)  # horas

                if not c11:
                    continue

                if c12.upper() == 'INSERSOR':
                    match = _match_pacote(c11)
                    if match and Discipline.query.filter_by(course_id=match.id).count() == 0:
                        cur_pac_id = match.id
                    else:
                        cur_pac_id = None
                    continue

                if cur_pac_id and c10.isdigit() and c11.upper() not in ('DISCIPLINAS', 'CH'):
                    _add_disc_concluida(cur_pac_id, int(c10), c11, f"{c14}h" if c14 else None)

            db.session.commit()

            # Pacotes 1-4: breakdown só existe como texto livre na coluna OBS,
            # curado manualmente (não segue o padrão do bloco lateral).
            OBS_MATRIZ_MANUAL = {
                'GAME LAB: COMPUTAÇÃO GRÁFICA, ANIMAÇÃO E PROGRAMAÇÃO': [
                    ('COMPUTAÇÃO GRÁFICA', '20h'),
                    ('ANIMAÇÃO PARA JOGOS: DOMINANDO A ARTE DO MOVIMENTO NO UNIVERSO DIGITAL', '20h'),
                    ('A ARTE DA PROGRAMAÇÃO DE JOGOS', '20h'),
                ],
                'CAPACITAÇÃO EM TUTORIA E MEDIAÇÃO PARA O SUCESSO ACADÊMICO': [
                    ('COMPETÊNCIAS DO TUTOR', '40h'),
                    ('IMPULSIONANDO O SUCESSO ACADÊMICO', '20h'),
                ],
                'TUTORIA EAD: COMPETÊNCIAS, PRÁTICAS E AÇÕES': [
                    ('EDUCAÇÃO A DISTÂNCIA E TUTORIA', '40h'),
                    ('COMPETÊNCIAS DO TUTOR', '40h'),
                    ('TUTORIA EM AÇÃO', '40h'),
                ],
                'APRENDIZAGEM NO ENSINO SUPERIOR: PRÁTICAS E INCLUSÃO': [
                    ('EDUCAÇÃO A DISTÂNCIA E TUTORIA', '40h'),
                    ('TÉCNICAS DE APRENDIZAGEM NO ENSINO SUPERIOR', '40h'),
                    ('PRINCÍPIOS BÁSICOS DO TDAH', '20h'),
                    ('IMPULSIONANDO O SUCESSO ACADÊMICO', '20h'),
                ],
            }
            for nome_pac, discs in OBS_MATRIZ_MANUAL.items():
                match = next((c for c in pacote_courses if nome_sim(c.nome, nome_pac)), None)
                if match and Discipline.query.filter_by(course_id=match.id).count() == 0:
                    for i, (nome_d, carga_d) in enumerate(discs, start=1):
                        _add_disc_concluida(match.id, i, nome_d, carga_d)
            db.session.commit()

            # ── Correlação com Rápidos ────────────────────────────────────
            # Quando uma disciplina de algum pacote corresponde a um curso
            # Rápido já cadastrado (mesmo nome), cria uma disciplina "espelho"
            # nesse Rápido (só se ele ainda não tiver nenhuma) — assim o Banco
            # de Disciplinas mostra a ocorrência em Rápido + Pacote(s) juntos,
            # em vez de só aparecer do lado do(s) pacote(s).
            rapido_courses = Course.query.filter_by(tipo='rapido').all()
            rapido_map_compact = {norm_compact(c.nome): c for c in rapido_courses}
            pac_disc_nomes = {}
            discs_pacotes = (Discipline.query
                              .join(Course, Discipline.course_id == Course.id)
                              .filter(Course.tipo == 'pacote').all())
            for d in discs_pacotes:
                pac_disc_nomes.setdefault(norm_compact(d.nome), d.nome)

            for chave, nome_orig in pac_disc_nomes.items():
                rap = rapido_map_compact.get(chave)
                if rap and Discipline.query.filter_by(course_id=rap.id).count() == 0:
                    carga_rap = f"{rap.horas}h" if rap.horas else None
                    _add_disc_concluida(rap.id, 1, rap.nome, carga_rap)

            db.session.commit()

        print("[OK] Dados importados com sucesso!")
    except FileNotFoundError:
        print("[INFO] Arquivo Excel nao encontrado.")
        db.session.rollback()
    except Exception as e:
        print(f"[ERRO] Ao importar Excel: {e}")
        db.session.rollback()

def seed_data():
    if User.query.count() == 0:
        # Senhas padrão temporárias — troca obrigatória no primeiro acesso.
        admin = User(username='admin', email='admin' + EMAIL_DOMINIO_PERMITIDO,
                     password=hash_pw('inova2024'), role='admin', must_change_password=True)
        junior = User(username='junior', email='junior' + EMAIL_DOMINIO_PERMITIDO,
                      password=hash_pw('inova2024'), role='editor', must_change_password=True)
        felipe = User(username='felipe', email='felipe' + EMAIL_DOMINIO_PERMITIDO,
                      password=hash_pw('inova2024'), role='editor', must_change_password=True)
        viewer = User(username='visualizador', email='visualizador' + EMAIL_DOMINIO_PERMITIDO,
                      password=hash_pw('inova2024'), role='viewer', must_change_password=True)
        db.session.add_all([admin, junior, felipe, viewer])
        db.session.commit()
    if Course.query.count() == 0:
        _import_excel()
    if VideoPreset.query.count() == 0:
        db.session.add_all([
            VideoPreset(label='Institucional', url='https://youtube.com/watch?v=xeKs2wZgL40', ordem=1),
            VideoPreset(label='Profissionalizantes / Rápidos', url='https://youtu.be/lT_Ii3nPXfc/', ordem=2),
            VideoPreset(label='Pós (Jorge)', url='https://youtu.be/0SAlaoAdIc4', ordem=3),
        ])
        db.session.commit()
    if VendaModalidadeOpcao.query.count() == 0:
        db.session.add_all([
            VendaModalidadeOpcao(label='Link', ordem=1),
            VendaModalidadeOpcao(label='Site', ordem=2),
        ])
        db.session.commit()
    # Ferramentas padrão — só semeia na primeira vez (tabela vazia). Checar
    # por label em vez de count==0 fazia uma ferramenta excluída pelo admin
    # voltar sozinha no próximo cold start do servidor, porque o rótulo
    # "sumia" da lista de existentes e o seed achava que faltava recriar.
    if ExternalTool.query.count() == 0:
        ferramentas_padrao = [
            ('Kronos', 'https://kronoslabtecie.web.app/'),
            ('Sistema Curadoria', 'https://sistema-curadoria.vercel.app/'),
            ('Moodle Graduação ERP', 'https://moodle.fatecie.edu.br/course/index.php?categoryid=11752'),
            ('Moodle Graduação WAE', 'https://www.eadunifatecie.com.br/'),
            ('Moodle Pós ERP', 'https://moodleposead.unifatecie.edu.br/login/index.php?loginredirect=1'),
            ('Moodle Cursos Técnicos ERP', 'https://moodle.evoluitec.app.br/course/index.php'),
            ('Moodle LAV', 'https://lav.eadunifatecie.com.br/login/index.php'),
            ('Microsoft Teams', 'https://teams.microsoft.com/'),
        ]
        for i, (label, url) in enumerate(ferramentas_padrao, start=1):
            db.session.add(ExternalTool(label=label, url=url, ordem=i))
        db.session.commit()

@app.route('/admin/importar-disciplinas', methods=['POST'])
@admin_required
def admin_importar_disciplinas():
    """Importa apenas disciplinas do Excel sem apagar dados existentes."""
    if _dados_ficticios_ativos():
        flash('Este ambiente tem dados fictícios gerados — importar da planilha real traria nome de verdade de volta. Use isso só num ambiente sem dado fictício.', 'danger')
        return redirect(url_for('dashboard'))
    try:
        total = _importar_so_disciplinas()
        flash(f'{total} disciplina(s) importada(s) com sucesso!', 'success')
    except Exception as e:
        flash(f'Erro ao importar disciplinas: {e}', 'danger')
    return redirect(url_for('dashboard'))

def _importar_ggbr_da_planilha():
    """Lê só a aba GGBR da planilha e cadastra os cursos que ainda não
    existem (confere por nome — não duplica se rodar de novo nem mexe em
    curso de nenhum outro tipo). GGBR é um curso "rápido" simples — sem
    módulos/disciplinas detalhados na planilha —, então a matriz dele vira
    uma única disciplina com o próprio nome do curso (mesmo padrão já
    usado pra Rápidos), só pra aparecer certo em Matrizes Curriculares.
    Roda pra todo curso GGBR sem disciplina nenhuma, novo ou já existente."""
    import re as _re3

    def limpar_horas(val):
        if val is None: return ''
        m = _re3.match(r'^(\d+\.?\d*)', str(val).strip())
        return m.group(1) if m else ''

    def limpar_valor(val):
        if val is None: return ''
        s = str(val).strip()
        return s if s not in ('-', '') else ''

    def is_numero(val):
        try: return int(str(val).strip()) > 0
        except: return False

    admin = User.query.filter_by(username='admin').first()
    admin_id = admin.id if admin else None

    existentes = {c.nome.strip().upper(): c for c in Course.query.filter_by(tipo='ggbr').all()}

    import openpyxl
    excel_path = os.path.join(os.path.dirname(__file__), 'CURSOS INOVA - LINKS (1).xlsx')
    wb = openpyxl.load_workbook(excel_path)

    total_cursos = 0
    total_discs = 0
    for shname in wb.sheetnames:
        if 'GGBR' in shname.upper():
            ws = wb[shname]
            for row in ws.iter_rows(min_row=2, values_only=True):
                if not is_numero(row[0]):
                    continue
                nome = str(row[1] or '').strip()
                if not nome:
                    continue
                chave = nome.upper()
                curso = existentes.get(chave)
                if not curso:
                    curso = Course(nome=nome[:300], tipo='ggbr', area=str(row[2] or '').strip()[:100],
                              horas=limpar_horas(row[3])[:20], valor=limpar_valor(row[5])[:50],
                              link_venda=str(row[4] or '').strip(), status='ativo',
                              insersor='INOVA', created_by=admin_id)
                    db.session.add(curso)
                    db.session.flush()  # pega o id do curso pra já criar a disciplina dele
                    existentes[chave] = curso
                    total_cursos += 1
                if Discipline.query.filter_by(course_id=curso.id).count() == 0:
                    horas_disc = limpar_horas(row[3])
                    db.session.add(Discipline(
                        course_id=curso.id, ordem=1, nome=nome[:300],
                        carga=f'{horas_disc}h' if horas_disc else None,
                        plataforma_ok=True, plataforma_em=datetime.utcnow(),
                    ))
                    total_discs += 1
            break
    db.session.commit()
    return total_cursos, total_discs

@app.route('/admin/importar-ggbr', methods=['POST'])
@admin_required
def admin_importar_ggbr():
    """Importa os cursos da aba GGBR da planilha que ainda não estão
    cadastrados e completa a matriz (1 disciplina por curso) de quem ainda
    não tinha — não mexe em nenhum outro tipo de curso nem duplica."""
    if _dados_ficticios_ativos():
        flash('Este ambiente tem dados fictícios gerados — importar da planilha real traria nome de verdade de volta. Use isso só num ambiente sem dado fictício.', 'danger')
        return redirect(url_for('dashboard'))
    try:
        total_cursos, total_discs = _importar_ggbr_da_planilha()
        if total_cursos or total_discs:
            log_action(session['user_id'], session['username'], 'importar', 'course', None,
                       f'GGBR: {total_cursos} curso(s) novo(s), {total_discs} disciplina(s) na matriz')
            partes = []
            if total_cursos: partes.append(f'{total_cursos} curso(s) novo(s)')
            if total_discs: partes.append(f'{total_discs} disciplina(s) na matriz')
            flash(' e '.join(partes) + ' importado(s) com sucesso!', 'success')
        else:
            flash('Nada novo pra importar — cursos e matriz GGBR já estavam completos.', 'info')
    except Exception as e:
        flash(f'Erro ao importar GGBR: {e}', 'danger')
    return redirect(url_for('cursos', tipo='ggbr'))

def _importar_so_disciplinas():
    import re as _re2, unicodedata as _ud2, openpyxl as _opx
    excel_path = os.path.join(os.path.dirname(__file__), 'CURSOS INOVA - LINKS (1).xlsx')
    if not os.path.exists(excel_path):
        raise FileNotFoundError('Arquivo Excel não encontrado.')
    wb = _opx.load_workbook(excel_path)

    def _norm(s):
        s = _re2.sub(r'\s+', ' ', str(s).upper().strip())
        return _re2.sub(r'\s+', ' ',
               ''.join(c for c in _ud2.normalize('NFKD', s) if not _ud2.combining(c))).strip()
    def _nc(s): return _re2.sub(r'\s+', '', _norm(s))
    def _sim(a, b):
        na, nb = _norm(a), _norm(b)
        if na == nb: return True
        ca, cb = _nc(a), _nc(b)
        if ca == cb: return True
        for n in [55, 50, 45, 40]:
            if len(ca) >= n and len(cb) >= n and ca[:n] == cb[:n]: return True
        for n in [45, 40, 35]:
            if len(na) >= n and len(nb) >= n and na[:n] == nb[:n]: return True
        return False
    def _cell(row, idx): return str(row[idx] or '').strip() if row and idx < len(row) else ''

    tit_lookup = {}
    if 'TITULAÇÕES PÓS' in wb.sheetnames:
        for row in wb['TITULAÇÕES PÓS'].iter_rows(min_row=2, values_only=True):
            if row[0] and len(row) > 4 and row[4]:
                tit_lookup[str(row[0]).strip().upper()] = str(row[4]).strip()

    total = 0

    # PÓS
    pos_courses = Course.query.filter_by(tipo='pos').all()
    sheet_m = next((s for s in wb.sheetnames if 'MATRIZES' in s.upper()), None)
    if sheet_m and pos_courses:
        ws = wb[sheet_m]
        all_rows = list(ws.iter_rows(min_row=3, values_only=True))
        mstart = next((i for i, r in enumerate(all_rows)
                       if not str(r[0] or '').strip().isdigit() and str(r[0] or '').strip()), len(all_rows))
        cur_id = None; in_disc = False; disc_ordem = 0; cur_mod = None
        for row in all_rows[mstart:]:
            c0,c1,c2,c3 = (_cell(row,i) for i in range(4))
            if not c0 and not c1 and not c2: in_disc = False; continue
            if c1.upper() == 'DISCIPLINAS': in_disc=True; disc_ordem=0; cur_mod=None; continue
            if not c0 and not c1 and c2: continue
            if not c2:
                cn = c0 if (c0 and not c1) else c1
                if cn and cn.upper() not in ('PROFESSOR','PROFESSORES','DISCIPLINAS'):
                    in_disc=False; disc_ordem=0; cur_mod=None; cur_id=None
                    m = next((c for c in pos_courses if _sim(c.nome, cn)), None)
                    if m and Discipline.query.filter_by(course_id=m.id).count()==0:
                        cur_id = m.id
                continue
            if in_disc and c1 and c2 and cur_id:
                if c0 and not c0.isdigit(): cur_mod=c0; disc_ordem+=1
                elif c0 and c0.isdigit(): disc_ordem=int(c0)
                else: disc_ordem+=1
                db.session.add(Discipline(course_id=cur_id, modulo=cur_mod,
                    ordem=disc_ordem, nome=c1, carga=c2 or None, professor=c3 or None,
                    titulacao=tit_lookup.get(c1.upper().strip(), '') or None))
                total += 1
        db.session.commit()

    # PROFISSIONALIZANTES
    prof_courses = Course.query.filter_by(tipo='profissionalizante').all()
    prof_map = {_norm(c.nome): c for c in prof_courses}
    prof_cmap = {_nc(c.nome): c for c in prof_courses}
    _STOPWORDS_PROF = {'DE','DA','DO','DAS','DOS','EM','NO','NA','NOS','NAS',
                        'PARA','COM','E','A','O','AO','AOS'}
    def _tok_prof(n):
        palavras = _re2.sub(r'\bIA\b', 'INTELIGENCIA ARTIFICIAL', _norm(n)).split()
        return frozenset(w for w in palavras if w not in _STOPWORDS_PROF)
    prof_semantico = {_tok_prof(c.nome): c for c in prof_courses}
    def _mp(n):
        if not n: return None
        if _norm(n) in prof_map: return prof_map[_norm(n)]
        if _nc(n) in prof_cmap: return prof_cmap[_nc(n)]
        for sz in [40,35,30,25,20]:
            for k,c in prof_cmap.items():
                if len(_nc(n))>=sz and len(k)>=sz and _nc(n)[:sz]==k[:sz]: return c
        tok = _tok_prof(n)
        if tok and tok in prof_semantico: return prof_semantico[tok]
        return None
    sheet_p = next((s for s in wb.sheetnames if 'PROFISSIONALIZANTE' in s.upper()), None)
    if sheet_p and prof_courses:
        # Os 2 blocos lado a lado da planilha NÃO ficam sincronizados na
        # mesma linha, então cada bloco é percorrido de forma independente
        # (ver mesmo comentário em _import_excel).
        rows_p = list(wb[sheet_p].iter_rows(min_row=1, values_only=True))

        def _parse_bloco_prof_topup(idx_a, idx_ordem, idx_nome, idx_carga):
            nonlocal total
            cur_id = None
            pendente = None
            modulo = None
            for row in rows_p:
                c_a = _cell(row, idx_a)
                c_o = _cell(row, idx_ordem)
                c_n = _cell(row, idx_nome)
                c_c = _cell(row, idx_carga)

                if c_n.upper() == 'DISCIPLINAS':
                    m = _mp(pendente) if pendente else None
                    cur_id = m.id if m and Discipline.query.filter_by(course_id=m.id).count() == 0 else None
                    modulo = None
                    pendente = None
                    continue

                if c_a and not c_a.startswith('Mód') and not c_n:
                    pendente = c_a
                    continue

                if c_a.startswith('Mód'):
                    modulo = c_a

                if c_o.isdigit() and c_n and c_n.upper() not in ('DISCIPLINAS', 'CH') and cur_id:
                    db.session.add(Discipline(course_id=cur_id, modulo=modulo,
                        ordem=int(c_o), nome=c_n, carga=c_c or None,
                        plataforma_ok=True, plataforma_em=datetime.utcnow()))
                    total += 1

        _parse_bloco_prof_topup(9, 10, 11, 12)
        _parse_bloco_prof_topup(14, 15, 16, 17)
        db.session.commit()

    # PACOTES — matriz (mesmo padrão de pós/profissionalizantes)
    pacote_courses = Course.query.filter_by(tipo='pacote').all()
    sheet_pac = next((s for s in wb.sheetnames if s.strip().upper() == 'PACOTE CURSOS'), None)
    if sheet_pac and pacote_courses:
        pac_map = {_norm(c.nome): c for c in pacote_courses}
        pac_cmap = {_nc(c.nome): c for c in pacote_courses}
        def _mpac(n):
            if not n: return None
            if _norm(n) in pac_map: return pac_map[_norm(n)]
            if _nc(n) in pac_cmap: return pac_cmap[_nc(n)]
            for sz in [40,35,30,25,20]:
                for k,c in pac_cmap.items():
                    if len(_nc(n))>=sz and len(k)>=sz and _nc(n)[:sz]==k[:sz]: return c
            return None

        def _add_disc_concluida(course_id, ordem, nome, carga, professor=None):
            db.session.add(Discipline(
                course_id=course_id, ordem=ordem, nome=nome, carga=carga or None,
                professor=professor, plataforma_ok=True, plataforma_em=datetime.utcnow()
            ))

        rows_pac = list(wb[sheet_pac].iter_rows(min_row=1, values_only=True))
        cur_pac_id = None
        for row in rows_pac:
            c10,c11,c12,c14 = _cell(row,10),_cell(row,11),_cell(row,12),_cell(row,14)
            if not c11:
                continue
            if c12.upper() == 'INSERSOR':
                m = _mpac(c11)
                cur_pac_id = m.id if m and Discipline.query.filter_by(course_id=m.id).count()==0 else None
                continue
            if cur_pac_id and c10.isdigit() and c11.upper() not in ('DISCIPLINAS','CH'):
                _add_disc_concluida(cur_pac_id, int(c10), c11, f"{c14}h" if c14 else None)
                total += 1
        db.session.commit()

        # Pacotes 1-4: breakdown só existe como texto livre na coluna OBS,
        # curado manualmente (não segue o padrão do bloco lateral).
        OBS_MATRIZ_MANUAL = {
            'GAME LAB: COMPUTAÇÃO GRÁFICA, ANIMAÇÃO E PROGRAMAÇÃO': [
                ('COMPUTAÇÃO GRÁFICA', '20h'),
                ('ANIMAÇÃO PARA JOGOS: DOMINANDO A ARTE DO MOVIMENTO NO UNIVERSO DIGITAL', '20h'),
                ('A ARTE DA PROGRAMAÇÃO DE JOGOS', '20h'),
            ],
            'CAPACITAÇÃO EM TUTORIA E MEDIAÇÃO PARA O SUCESSO ACADÊMICO': [
                ('COMPETÊNCIAS DO TUTOR', '40h'),
                ('IMPULSIONANDO O SUCESSO ACADÊMICO', '20h'),
            ],
            'TUTORIA EAD: COMPETÊNCIAS, PRÁTICAS E AÇÕES': [
                ('EDUCAÇÃO A DISTÂNCIA E TUTORIA', '40h'),
                ('COMPETÊNCIAS DO TUTOR', '40h'),
                ('TUTORIA EM AÇÃO', '40h'),
            ],
            'APRENDIZAGEM NO ENSINO SUPERIOR: PRÁTICAS E INCLUSÃO': [
                ('EDUCAÇÃO A DISTÂNCIA E TUTORIA', '40h'),
                ('TÉCNICAS DE APRENDIZAGEM NO ENSINO SUPERIOR', '40h'),
                ('PRINCÍPIOS BÁSICOS DO TDAH', '20h'),
                ('IMPULSIONANDO O SUCESSO ACADÊMICO', '20h'),
            ],
        }
        for nome_pac, discs in OBS_MATRIZ_MANUAL.items():
            match = next((c for c in pacote_courses if _sim(c.nome, nome_pac)), None)
            if match and Discipline.query.filter_by(course_id=match.id).count() == 0:
                for i, (nome_d, carga_d) in enumerate(discs, start=1):
                    _add_disc_concluida(match.id, i, nome_d, carga_d)
                    total += 1
        db.session.commit()

        # Correlação com Rápidos: quando uma disciplina de algum pacote
        # corresponde a um curso Rápido já cadastrado (mesmo nome), cria uma
        # disciplina "espelho" nesse Rápido (só se ainda não tiver nenhuma) —
        # assim o Banco de Disciplinas mostra a ocorrência em Rápido +
        # Pacote(s) juntos.
        rapido_courses = Course.query.filter_by(tipo='rapido').all()
        rapido_cmap = {_nc(c.nome): c for c in rapido_courses}
        pac_disc_nomes = {}
        discs_pacotes = (Discipline.query
                          .join(Course, Discipline.course_id == Course.id)
                          .filter(Course.tipo == 'pacote').all())
        for d in discs_pacotes:
            pac_disc_nomes.setdefault(_nc(d.nome), d.nome)

        for chave, nome_orig in pac_disc_nomes.items():
            rap = rapido_cmap.get(chave)
            if rap and Discipline.query.filter_by(course_id=rap.id).count() == 0:
                carga_rap = f"{rap.horas}h" if rap.horas else None
                _add_disc_concluida(rap.id, 1, rap.nome, carga_rap)
                total += 1
        db.session.commit()

    return total


def _corrigir_matriz_profissionalizantes():
    """Reconstrói do zero a matriz de TODOS os cursos Profissionalizantes.

    Corrige um bug de importação: os 2 blocos lado a lado da planilha
    "PROFISSIONALIZANTES INOVA" não ficam sincronizados na mesma linha (um
    curso pode ter mais ou menos disciplinas que o vizinho), e a extração
    antiga tratava o cabeçalho "DISCIPLINAS" de qualquer um dos blocos como
    ponto de sincronização dos dois — quando os blocos não coincidiam, um
    bloco "roubava" o nome de curso do outro e a matriz saía incompleta
    (em alguns casos com só 1 disciplina, em vez de 6 a 8).

    Como o import normal (_importar_so_disciplinas) só preenche cursos que
    ainda não têm nenhuma disciplina, ele nunca corrigiria os que já tinham
    uma matriz (mesmo que errada) — por isso este reparo apaga e reconstrói
    a matriz (só as disciplinas, nenhum outro dado é tocado), já marcando
    tudo como concluído na plataforma.
    """
    import re as _re2, unicodedata as _ud2, openpyxl as _opx
    excel_path = os.path.join(os.path.dirname(__file__), 'CURSOS INOVA - LINKS (1).xlsx')
    if not os.path.exists(excel_path):
        raise FileNotFoundError('Arquivo Excel não encontrado.')
    wb = _opx.load_workbook(excel_path)

    def _norm(s):
        s = _re2.sub(r'\s+', ' ', str(s).upper().strip())
        return _re2.sub(r'\s+', ' ',
               ''.join(c for c in _ud2.normalize('NFKD', s) if not _ud2.combining(c))).strip()
    def _nc(s): return _re2.sub(r'\s+', '', _norm(s))
    def _cell(row, idx): return str(row[idx] or '').strip() if row and idx < len(row) else ''

    prof_courses = Course.query.filter_by(tipo='profissionalizante').all()
    sheet_p = next((s for s in wb.sheetnames if 'PROFISSIONALIZANTE' in s.upper()), None)
    if not sheet_p or not prof_courses:
        return 0

    prof_map = {_norm(c.nome): c for c in prof_courses}
    prof_cmap = {_nc(c.nome): c for c in prof_courses}
    _STOPWORDS_PROF = {'DE','DA','DO','DAS','DOS','EM','NO','NA','NOS','NAS',
                        'PARA','COM','E','A','O','AO','AOS'}
    def _tok_prof(n):
        palavras = _re2.sub(r'\bIA\b', 'INTELIGENCIA ARTIFICIAL', _norm(n)).split()
        return frozenset(w for w in palavras if w not in _STOPWORDS_PROF)
    prof_semantico = {_tok_prof(c.nome): c for c in prof_courses}
    def _mp(n):
        if not n: return None
        if _norm(n) in prof_map: return prof_map[_norm(n)]
        if _nc(n) in prof_cmap: return prof_cmap[_nc(n)]
        for sz in [40, 35, 30, 25, 20]:
            for k, c in prof_cmap.items():
                if len(_nc(n)) >= sz and len(k) >= sz and _nc(n)[:sz] == k[:sz]: return c
        tok = _tok_prof(n)
        if tok and tok in prof_semantico: return prof_semantico[tok]
        return None

    # Apaga só as disciplinas desses cursos (nenhum outro dado é alterado)
    # pra reconstruir a matriz do zero com o parser corrigido.
    for c in prof_courses:
        Discipline.query.filter_by(course_id=c.id).delete(synchronize_session=False)
    db.session.commit()
    db.session.expire_all()

    rows_p = list(wb[sheet_p].iter_rows(min_row=1, values_only=True))
    total = 0

    def _parse_bloco(idx_a, idx_ordem, idx_nome, idx_carga):
        nonlocal total
        cur_id = None
        pendente = None
        modulo = None
        for row in rows_p:
            c_a = _cell(row, idx_a)
            c_o = _cell(row, idx_ordem)
            c_n = _cell(row, idx_nome)
            c_c = _cell(row, idx_carga)

            if c_n.upper() == 'DISCIPLINAS':
                m = _mp(pendente) if pendente else None
                cur_id = m.id if m else None
                modulo = None
                pendente = None
                continue

            if c_a and not c_a.startswith('Mód') and not c_n:
                pendente = c_a
                continue

            if c_a.startswith('Mód'):
                modulo = c_a

            if c_o.isdigit() and c_n and c_n.upper() not in ('DISCIPLINAS', 'CH') and cur_id:
                db.session.add(Discipline(
                    course_id=cur_id, modulo=modulo, ordem=int(c_o), nome=c_n,
                    carga=c_c or None, plataforma_ok=True, plataforma_em=datetime.utcnow()
                ))
                total += 1

    _parse_bloco(9, 10, 11, 12)
    _parse_bloco(14, 15, 16, 17)
    db.session.commit()
    return total


@app.route('/admin/corrigir-matriz-profissionalizantes', methods=['POST'])
@admin_required
def admin_corrigir_matriz_profissionalizantes():
    """Reconstrói a matriz de todos os Profissionalizantes a partir do Excel,
    corrigindo cursos que ficaram com matriz incompleta pelo bug de
    desalinhamento entre os 2 blocos da planilha. Preserva o status "na
    plataforma" já marcado."""
    if _dados_ficticios_ativos():
        flash('Este ambiente tem dados fictícios gerados — importar da planilha real traria nome de verdade de volta. Use isso só num ambiente sem dado fictício.', 'danger')
        return redirect(url_for('dashboard'))
    try:
        total = _corrigir_matriz_profissionalizantes()
        flash(f'Matriz de Profissionalizantes reconstruída — {total} disciplina(s).', 'success')
    except Exception as e:
        flash(f'Erro ao corrigir matriz: {e}', 'danger')
    return redirect(url_for('dashboard'))


# ─── INIT ──────────────────────────────────────────────────────────────────────

_db_ready = False

def _run_migrations():
    """Adiciona colunas que podem estar faltando em bancos mais antigos."""
    is_pg = _db_url.startswith('postgresql://')
    # Para PostgreSQL usa IF NOT EXISTS; para SQLite captura exceção
    migrations = [
        ("refund",     "concluido_manual", "BOOLEAN DEFAULT false"),
        ("refund",     "cpf",              "VARCHAR(20)"),
        ("refund",     "celular",          "VARCHAR(30)"),
        ("refund",     "pix",              "VARCHAR(200)"),
        ("refund",     "email_destino",    "VARCHAR(200)"),
        ("course",     "dono",             "TEXT"),
        ("course",     "ano",              "VARCHAR(10)"),
        ("course",     "extra_data",       "TEXT"),
        ("course",     "venda_modalidade", "VARCHAR(100)"),
        ("course",     "data_finalizacao", "DATE"),
        ("course",     "link_video",       "TEXT"),
        ("course",     "limite_parcelas",  "VARCHAR(10)"),
        ("course",     "via_formulario",   "BOOLEAN DEFAULT false"),
        ("course",     "categoria",        "VARCHAR(30) DEFAULT 'INOVA'"),
        ("external_tool", "embeddable",             "BOOLEAN"),
        ("external_tool", "embeddable_checado_em",  "TIMESTAMP"),
        ("mural_mensagem", "resposta_a_id", "INTEGER"),
        ("mural_mensagem", "mencionado_id", "INTEGER"),
        ("mural_mensagem", "editado_em",    "TIMESTAMP"),
        ("mural_mensagem", "privada",       "BOOLEAN DEFAULT false"),
        ("discipline", "cod_moodle",       "VARCHAR(50)"),
        ("discipline", "titulacao",        "VARCHAR(50)"),
        ("discipline", "plataforma_ok",    "BOOLEAN DEFAULT false"),
        ("discipline", "plataforma_em",    "TIMESTAMP"),
        ("backup_record", "conteudo",      "BYTEA"),
        ("demanda", "responsaveis",        "TEXT"),
        ("demanda", "alerta_texto",        "TEXT"),
        ("demanda", "alerta_ativo",        "BOOLEAN DEFAULT false"),
        ("demanda", "alerta_criado_em",    "TIMESTAMP"),
        ("demanda", "alerta_criado_por",   "INTEGER"),
        ("demanda", "alerta_whatsapp",         "BOOLEAN DEFAULT false"),
        ("demanda", "alerta_whatsapp_enviado", "BOOLEAN DEFAULT false"),
        ("lembrete_fixo", "ultimo_checkin_ocorrencia", "DATE"),
        ("lembrete_fixo", "avisar_whatsapp", "BOOLEAN DEFAULT false"),
        ("lembrete_fixo", "ultimo_whatsapp_ocorrencia", "DATE"),
        ("disciplina_modulo", "submodulo", "VARCHAR(200)"),
        ("disciplina_modulo", "carga",     "VARCHAR(20)"),
        ("disciplina_modulo", "professor", "VARCHAR(200)"),
        ("disciplina_modulo", "arquivado", "BOOLEAN DEFAULT false"),
    ]
    with db.engine.connect() as conn:
        for table, col, dtype in migrations:
            try:
                if is_pg:
                    sql = f'ALTER TABLE {table} ADD COLUMN IF NOT EXISTS {col} {dtype}'
                else:
                    sql = f'ALTER TABLE {table} ADD COLUMN {col} {dtype}'
                conn.execute(db.text(sql))
                conn.commit()
            except Exception:
                try:
                    conn.rollback()
                except Exception:
                    pass
        # venda_modalidade nasceu VARCHAR(10) (só "link"/"site"); agora aceita
        # opções com nome livre e mais longo, então alarga a coluna existente
        if is_pg:
            try:
                conn.execute(db.text('ALTER TABLE course ALTER COLUMN venda_modalidade TYPE VARCHAR(100)'))
                conn.commit()
            except Exception:
                try:
                    conn.rollback()
                except Exception:
                    pass
        # tabela "user" precisa de aspas pois é palavra reservada em alguns DBs
        for col, dtype in [("permissoes", "TEXT DEFAULT '{}' "), ("email", "VARCHAR(200)"),
                           ("must_change_password", "BOOLEAN DEFAULT false"),
                           ("nome", "VARCHAR(200)"),
                           ("dashboard_prefs", "TEXT"),
                           ("notas_pessoais", "TEXT"),
                           ("equipe", "BOOLEAN DEFAULT true"), ("foto", "BYTEA"),
                           ("foto_mimetype", "VARCHAR(50)"), ("ultimo_login", "TIMESTAMP"),
                           ("telefone_whatsapp", "VARCHAR(30)"), ("whatsapp_prefs", "TEXT"),
                           ("whatsapp_apikey", "VARCHAR(50)"), ("agenda_ics_url", "TEXT"),
                           ("agenda_ics_visibilidade", "VARCHAR(20) DEFAULT 'pessoal'"),
                           ("agenda_cache_json", "TEXT"), ("agenda_cache_em", "TIMESTAMP")]:
            try:
                tbl = '"user"' if is_pg else 'user'
                sql = f'ALTER TABLE {tbl} ADD COLUMN {col} {dtype}'
                if is_pg:
                    sql = f'ALTER TABLE "user" ADD COLUMN IF NOT EXISTS {col} {dtype}'
                conn.execute(db.text(sql))
                conn.commit()
            except Exception:
                try:
                    conn.rollback()
                except Exception:
                    pass
        # Feature "Destaque da Semana/Mês" foi removida de vez — apaga a
        # tabela (e os registros que ela guardava) se ainda existir.
        try:
            conn.execute(db.text('DROP TABLE IF EXISTS destaque'))
            conn.commit()
        except Exception:
            try:
                conn.rollback()
            except Exception:
                pass

        # SubmoduloCalendario (Módulo) mudou de "um por Tipo" pra uma lista
        # global — só derruba a tabela antiga se ela ainda estiver vazia
        # (nunca apaga dado real, só a estrutura de um schema que não
        # chegou a ser usado). db.create_all() recria com o schema novo.
        try:
            total = conn.execute(db.text('SELECT COUNT(*) FROM submodulo_calendario')).scalar()
            if total == 0:
                conn.execute(db.text('DROP TABLE submodulo_calendario'))
                conn.commit()
        except Exception:
            try:
                conn.rollback()
            except Exception:
                pass
    db.create_all()

    # Correção de segurança: hash de senha em SHA-256 puro (sem sal, sem
    # custo computacional) é mais fraco que pbkdf2/scrypt — o login já
    # promove pro formato novo sozinho quando a pessoa entra (ver
    # check_pw), mas quem não logou desde essa correção continua com o
    # hash antigo guardado. Força troca de senha nessas contas: no
    # próximo login o hash sobe de nível E a pessoa escolhe senha nova.
    try:
        legado = User.query.filter(
            ~User.password.startswith('pbkdf2:'), ~User.password.startswith('scrypt:'),
            User.must_change_password == False,
        ).all()
        for u in legado:
            u.must_change_password = True
        if legado:
            db.session.commit()
    except Exception:
        try:
            db.session.rollback()
        except Exception:
            pass


@app.before_request
def ensure_db():
    global _db_ready
    if not _db_ready:
        try:
            db.create_all()
            _run_migrations()
            seed_data()
            # Limpeza pontual: algum import antigo pode ter gravado a string
            # literal "None" em vez de deixar o campo vazio de verdade.
            User.query.filter(User.nome == 'None').update({'nome': None})
            db.session.commit()
            _db_ready = True
        except Exception:
            import traceback
            traceback.print_exc()  # detalhe completo só no log do servidor, nunca pro navegador
            return "Erro ao conectar com o banco de dados. Tente novamente em instantes.", 500

ROTAS_LIVRES_TROCA_SENHA = {'minha_conta', 'logout', 'login', 'static', 'esqueci_senha', 'resetar_senha'}

@app.before_request
def exigir_troca_senha():
    if request.endpoint in ROTAS_LIVRES_TROCA_SENHA or request.endpoint is None:
        return
    if 'user_id' not in session:
        return
    u = User.query.get(session['user_id'])
    if u and u.must_change_password and u.can_change_own_password() and not u.is_conta_demo():
        flash('Por segurança, troque sua senha antes de continuar.', 'danger')
        return redirect(url_for('minha_conta'))

@app.after_request
def _security_headers(resp):
    """Cabeçalhos de segurança básicos — nenhum muda comportamento visível.
    X-Frame-Options/frame-ancestors bloqueiam o sistema de ser embutido em
    iframe de outro site (clickjacking); X-Content-Type-Options impede o
    navegador de "adivinhar" tipo de arquivo diferente do declarado;
    Referrer-Policy evita vazar a URL completa pra terceiros. O CSP libera
    só o que o próprio sistema já usa de verdade: scripts/estilos inline
    (o app inteiro depende disso hoje), Google Fonts, o Chart.js do cdnjs
    e iframes https (usado pela tela de Ferramentas Externas embutidas)."""
    resp.headers['X-Frame-Options'] = 'DENY'
    resp.headers['X-Content-Type-Options'] = 'nosniff'
    resp.headers['Referrer-Policy'] = 'strict-origin-when-cross-origin'
    resp.headers['Content-Security-Policy'] = (
        "default-src 'self'; "
        "script-src 'self' 'unsafe-inline' https://cdnjs.cloudflare.com; "
        "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; "
        "font-src 'self' https://fonts.gstatic.com; "
        "img-src 'self' data: https:; "
        "frame-src https:; "
        "frame-ancestors 'none'"
    )
    if _db_url.startswith('postgresql://'):
        resp.headers['Strict-Transport-Security'] = 'max-age=31536000; includeSubDomains'
    return resp

@app.after_request
def _nunca_cachear_paginas_dinamicas(resp):
    """A Vercel aplica por padrão 'public, max-age=0, must-revalidate' nas
    respostas do Python — em teoria isso força revalidação a cada acesso,
    mas na prática já causou tela desatualizada em navegador/CDN mais de
    uma vez (ex: aviso vermelho do topo só sumindo com refresh forçado).
    Como é tudo dado dinâmico e por sessão, força 'no-store' de verdade em
    qualquer resposta que não seja arquivo estático."""
    if not request.path.startswith('/static/'):
        resp.headers['Cache-Control'] = 'no-store, no-cache, must-revalidate'
        resp.headers['Pragma'] = 'no-cache'
    return resp

ROTAS_LIVRES_ERP_MOODLE = {
    'erp_moodle', 'erp_moodle_novo', 'erp_moodle_editar', 'erp_moodle_excluir',
    'minha_conta', 'logout', 'login', 'static', 'esqueci_senha', 'resetar_senha',
}

@app.before_request
def restringir_somente_erp_moodle():
    """Contas da equipe externa (permissão 'somente_erp_moodle') não podem
    navegar pra nenhuma outra tela do sistema — nem dashboard, cursos,
    financeiro etc. Ficam presas na tela do ERP Moodle e em 'Minha Conta'."""
    if request.endpoint in ROTAS_LIVRES_ERP_MOODLE or request.endpoint is None:
        return
    if 'user_id' not in session:
        return
    u = User.query.get(session['user_id'])
    if u and u.is_restrito_erp_moodle():
        return redirect(url_for('erp_moodle'))

# Rotas de relatório/exportação — indisponíveis pra conta de demonstração,
# tanto pra não vazar valor quanto pra não gerar carga de exportação à toa.
ROTAS_RELATORIO_EXPORT_DEMO = {
    'cursos_exportar_excel', 'cursos_relatorio',
    'reembolsos_exportar_excel', 'pagamentos_terceiros_exportar_excel',
    'banco_disciplinas_exportar_excel', 'banco_disciplinas_relatorio',
    'matrizes_relatorio', 'matrizes_exportar_excel',
    'formulario_exportar', 'calendario_exportar', 'calendario_disciplinas_exportar',
}

@app.before_request
def restringir_conta_demo():
    """Conta de demonstração (permissão 'conta_demo'): só navega/visualiza.
    Qualquer POST (criar/editar/excluir/ações em lote) é barrado aqui de uma
    vez, sem precisar mexer rota por rota; telas de criar/editar (GET) e
    relatório/exportação também ficam fora — ela só troca de tela."""
    if request.endpoint is None or 'user_id' not in session:
        return
    u = User.query.get(session['user_id'])
    if not (u and u.is_conta_demo()):
        return
    bloquear = (
        request.method == 'POST'
        or request.endpoint in ROTAS_RELATORIO_EXPORT_DEMO
        or request.endpoint.endswith('_novo')
        or request.endpoint.endswith('_editar')
    )
    if bloquear:
        flash('Conta de demonstração — essa ação não está disponível, só a navegação entre telas.', 'warning')
        return redirect(url_for('dashboard'))

@app.after_request
def sem_cache_paginas_dinamicas(response):
    """Sem isso, o navegador (ou algum cache no meio do caminho) pode
    mostrar uma versão antiga da página numa navegação normal — foi o que
    fazia o aviso vermelho de Demanda/lembrete sumir sozinho até dar um
    refresh forte. Arquivos estáticos (/static/...) já têm cache-busting
    por versão (?v=) e continuam cacheáveis normalmente."""
    if not request.path.startswith('/static/'):
        response.headers['Cache-Control'] = 'no-store, no-cache, must-revalidate, max-age=0'
        response.headers['Pragma'] = 'no-cache'
    return response

@app.errorhandler(Exception)
def erro_nao_tratado(e):
    """Pega qualquer exceção não tratada em qualquer rota, avisa por
    WhatsApp quem tiver ligado 'erros_plataforma' em Minha Conta, e só
    depois deixa o erro seguir seu caminho normal — nunca some com o
    traceback do log do servidor nem muda o comportamento de erros HTTP
    normais (404, 403 etc.), só de exceção mesmo."""
    if isinstance(e, HTTPException):
        return e
    try:
        _notificar_erro_plataforma(e)
    except Exception:
        pass
    import traceback
    traceback.print_exc()
    return 'Erro interno. Tente novamente em instantes.', 500

if __name__ == '__main__':
    t = threading.Thread(target=backup_scheduler, daemon=True)
    t.start()
    port = int(os.environ.get('PORT', 5000))
    app.run(debug=False, host='0.0.0.0', port=port)
