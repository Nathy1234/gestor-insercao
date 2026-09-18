# 🎓 Gestor da Equipe de Inserção — Gestor Acadêmico

Sistema interno da equipe de Inserção pra controlar o que é inserido na Inova
Carreira e nos Moodles, substituindo o controle por planilhas soltas: catálogo
de cursos, matrizes curriculares, banco de disciplinas, calendário de demandas,
financeiro (reembolsos, pagamentos a terceiros, cupons), dashboard pessoal por
responsável, mural da equipe, formulários internos e um assistente de consulta
em linguagem natural sobre a própria base de dados.

Em produção desde maio de 2026 (o projeto em si começou em março, ainda como
uma simples organização dos dados da Inova Carreira, e foi evoluindo até virar
isto aqui).

---

## 🚀 Como rodar localmente

### 1. Pré-requisitos
- Python 3.10+ ([python.org](https://python.org))
- Um ambiente virtual (`venv`) é recomendado

### 2. Instalar dependências

\`\`\`bash
python -m venv .venv
.venv\Scripts\activate        # Windows
# source .venv/bin/activate   # Mac/Linux
pip install -r requirements.txt
\`\`\`

### 3. Rodar o sistema

\`\`\`bash
python app.py
\`\`\`

Acesse em `http://localhost:5000`.

> **Sobre o banco de dados local:** rodar `python app.py` sem nenhuma variável
> de ambiente extra usa automaticamente um banco **SQLite isolado**
> (`inova.db`, criado na primeira execução) — nunca o banco de produção. Isso é
> proposital: o carregamento do `.env` (se você tiver um) ignora de propósito
> `DATABASE_URL` e `SECRET_KEY`, então mesmo com um `.env` de produção na pasta,
> uma execução local não toca nos dados reais por engano. Só usa o banco real
> se `DATABASE_URL` estiver definida como variável de ambiente do próprio
> sistema operacional.

Na primeira execução, o sistema cria sozinho (`seed_data()`):
- 4 usuários padrão (tabela abaixo)
- Ferramentas externas padrão (Kronos, Moodles, Curadoria, Teams)
- Opções de "Venda por" (Link, Site)
- Tenta importar cursos de um arquivo `CURSOS INOVA - LINKS (1).xlsx` na raiz
  do projeto, se ele existir — sem esse arquivo, o sistema sobe normalmente,
  só sem cursos de exemplo.

---

## 🔑 Usuários padrão (criados automaticamente)

| Usuário         | Senha       | Perfil  |
|-----------------|-------------|---------|
| `admin`         | `inova2024` | Admin   |
| `junior`        | `inova2024` | Editor  |
| `felipe`        | `inova2024` | Editor  |
| `visualizador`  | `inova2024` | Leitor  |

Todos nascem com `must_change_password=True` — a troca de senha é obrigatória
no primeiro acesso, o sistema não deixa passar disso.

---

## 📋 Módulos do sistema

- **Cursos** — catálogo completo (tipo, área, carga horária, valor, canal de
  venda), edição em lote, filtros, relatório e exportação Excel. Cobre os 11
  tipos da Inova Carreira: Pós, Profissionalizante, Rápido, Pacote, Terceiros,
  Evento, Prática Conectada, Prática Estágio, Projeto Ambiental, GGBR e
  Integra Edu.
- **ERP Moodle** — acompanhamento separado de disciplinas inseridas nos
  ambientes Moodle (status em inserção/concluída, responsável).
- **Matrizes Curriculares** — módulos e disciplinas por curso, importação em
  massa colando do Excel/Sheets, e sugestão automática de matriz a partir do
  curso existente mais parecido.
- **Banco de Disciplinas** — agrupa disciplinas com o mesmo nome entre cursos
  diferentes, mostrando onde cada uma se repete.
- **IA Assistente** — perguntas em linguagem natural sobre a base de dados
  (casamento de padrões + consulta dinâmica ao banco; sem LLM externo hoje).
- **Calendário de Demandas** — prazos, responsáveis, avisos manuais
  dispensáveis, lembretes fixos mensais e link público (sem login) com o
  andamento das disciplinas, geral ou filtrado por tipo.
- **Dashboard pessoal** — cada um vê "Meus Cursos"; admin vê a visão
  consolidada da equipe inteira, reembolsos pendentes, notas rápidas e
  histórico de atividades recentes.
- **Financeiro** — Reembolsos (com etapa calculada automaticamente),
  Pagamentos a Terceiros e Cupons.
- **Mural da Equipe** — recados com reação, resposta e mensagem privada.
- **Formulários internos** — pesquisas com indicadores (média/distribuição)
  calculados automaticamente.
- **Ferramentas Externas** — links centralizados (Moodles, Curadoria, Kronos,
  Teams), alguns embutidos via iframe.
- **Histórico / Auditoria** — toda ação relevante fica registrada.
- **Backup** — automático diário (via Vercel Cron em produção), manual a
  qualquer momento, restauração protegida por frase de confirmação.
- **Permissões** — por papel (admin/editor/leitor) e, além disso,
  individualmente por pessoa e por módulo.

---

## 🔒 Segurança

- Senhas sempre com hash (`pbkdf2`/`scrypt`), nunca em texto puro.
- Login restrito a e-mail institucional (`@fatecie.edu.br`).
- Rate limit em login, redefinição de senha e formulário público de evento.
- CSRF ativo globalmente (Flask-WTF).
- Toda operação que apaga/sobrescreve dado é sempre `POST`.
- Headers de segurança (`X-Frame-Options`, `Content-Security-Policy`,
  `X-Content-Type-Options`, `Strict-Transport-Security` em produção).
- Upload de imagem validado pela assinatura real do arquivo, não pelo
  mimetype informado pelo navegador.
- Erro de conexão com banco nunca aparece pro usuário, só no log do servidor.

---

## 🌐 Deploy (produção)

Deploy automático via Vercel a cada `git push origin main`
(veja `vercel.json`). Variáveis de ambiente necessárias no painel da Vercel:

| Variável | Uso |
|---|---|
| `DATABASE_URL` | Conexão com o PostgreSQL (Supabase) — **nunca** via `.env` local |
| `SECRET_KEY` | Assinatura de sessão — **nunca** via `.env` local |
| `EMAIL_SMTP_USER` / `EMAIL_SMTP_PASSWORD` | Conta Gmail usada pra e-mails (reset de senha, backup, reembolso) |
| `CRON_SECRET` | Protege a rota `/cron/backup` chamada pelo Vercel Cron |
| `ANTHROPIC_API_KEY` | Reservada pra uma futura versão do IA Assistente com LLM — ainda não usada no código |

Este repositório é o **ambiente de produção** — existe um par de teste
totalmente isolado (repositório, Vercel e banco de dados próprios) usado pra
validar mudanças arriscadas antes de trazer pra cá. Detalhes desse fluxo estão
no `CLAUDE.md`.

---

## 🗂️ Estrutura do Projeto

\`\`\`
inova_system/
├── app.py              ← Aplicação inteira (rotas, modelos, lógica de negócio)
├── requirements.txt    ← Dependências Python
├── vercel.json          ← Config de deploy e cron job da Vercel
├── static/
│   ├── css/style.css   ← Design do sistema (tema claro/escuro)
│   └── js/app.js       ← Editor de matriz, dashboard, toasts, busca global
└── templates/          ← ~40 páginas HTML (uma por tela/módulo)
\`\`\`

## 🧰 Stack técnica

Python (Flask) + SQLAlchemy · PostgreSQL (Supabase) em produção / SQLite em
desenvolvimento · Flask-WTF (CSRF) · Flask-Limiter (rate limit) · openpyxl
(Excel) · icalendar (agenda pessoal) · deploy contínuo via Vercel.
