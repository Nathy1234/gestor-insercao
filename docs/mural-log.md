# Log da equipe no mural

O mural mantém os recados e conversas existentes e estende a aba de Logs existente
com a coleta automática, preservando o registro manual e a exportação para texto.
A aba **Log externo** mostra somente novidades externas: Teams e planilhas monitoradas. Atividades
do próprio Gestor não entram nessa aba. Conversas entre duas pessoas também ficam
fora do log.

O coletor consulta Microsoft Graph com acesso **delegado à titular**. Confere `/me`,
lista seus grupos e equipes e descarta chats `oneOnOne` antes de ler mensagens.
Grupos e reuniões precisam ter pelo menos três membros e incluir a titular.
Canais privados/compartilhados precisam de associação confirmada. Respostas,
edições e exclusões de mensagens também entram. Um evento é identificado por uma
chave única; reenvios não duplicam registros.

Planilhas XLSX configuradas ou compartilhadas por links SharePoint nas mensagens
novas são monitoradas em todas as abas, inclusive ocultas. A primeira leitura cria
uma referência, sem atribuir alterações antigas a alguém. Nas leituras seguintes,
o log informa as abas e células alteradas. O último editor informado pela Microsoft
é apresentado como informação do arquivo, não como autor de cada célula. O banco
guarda hashes das células, não seu conteúdo. Cursos não precisam estar cadastrados
no Gestor para que sua aba seja monitorada; o coletor não cadastra cursos.

## Ativação (testar primeiro no repositório de teste)

1. Registrar um aplicativo web no tenant institucional Microsoft. Obter consentimento
   delegado para `offline_access`, `User.Read`, `Chat.Read`, `ChatMember.Read`,
   `Team.ReadBasic.All`, `Channel.ReadBasic.All`, `ChannelMember.Read.All`,
   `ChannelMessage.Read.All`, `Files.Read.All` e, para resolver compartilhamentos,
   `Sites.Read.All`. A política institucional pode exigir um administrador.
   Obter um refresh token por um fluxo OAuth autorizado. Nunca colar tokens em chat,
   commits ou relatórios. Esta alteração não contém uma tela OAuth: esse passo ainda
   precisa ser realizado pela configuração da integração.
2. No servidor Gestor, configurar `MURAL_SYNC_SECRET` (aleatório, pelo menos 32
   caracteres) e `MS_GRAPH_USER_ID` (ID da titular no Microsoft Graph).
3. No GitHub Actions, configurar os secrets `MURAL_SYNC_SECRET`,
   `MS_GRAPH_CLIENT_SECRET`, `MS_GRAPH_REFRESH_TOKEN`. Configurar as variables
   `GESTOR_URL`, `MS_GRAPH_USER_ID`, `MS_GRAPH_TENANT_ID`, `MS_GRAPH_CLIENT_ID`,
   `MURAL_SPREADSHEETS_JSON` e opcionalmente `MURAL_SYNC_START` (ISO 8601 com fuso).
   O ID da titular precisa coincidir nos dois ambientes.
4. `MURAL_SPREADSHEETS_JSON` é um array de arquivos confirmados:
   `[{"nome":"Inserção Geral","drive_id":"ID","item_id":"ID"}]`.
   Também aceita `{"id":"identidade-estavel","nome":"Links INOVA","url":"https://tenant.sharepoint.com/..."}`.
   Confirmar os links das planilhas ativas; cópias antigas de planilhas não equivalem
   à fonte em uso. Google Sheets, CSV e arquivos locais não estão cobertos nesta versão.
5. Definir `MURAL_SYNC_ENABLED=true` e executar manualmente o workflow no teste.
   Conferir eventos, uma segunda execução sem duplicatas e uma alteração de célula.
   O cron é horário, no minuto 17, e só funciona quando o workflow está no branch
   padrão. GitHub pode atrasar execuções agendadas; não é uma garantia de minuto exato.
6. Depois da validação, levar somente o commit validado à produção e configurar
   os valores próprios desse ambiente. Nunca compartilhar banco ou credenciais
   entre teste e produção. O agendamento fica desativado enquanto a variable estiver
   ausente. O log externo só estará ativo após a primeira verificação bem-sucedida.

## Limites e falhas

As consultas registram as fontes que falharam no mural e preservam seus cursores.
Falhas de autenticação ou indisponibilidade total podem impedir até esse aviso;
a ausência de uma verificação recente indica interrupção. Refresh tokens podem
expirar ou ser revogados: renová-los através do fluxo OAuth. O token renovado
retornado pela Microsoft não é persistido pelo workflow; seguir a política de
rotação do tenant e substituir o secret periodicamente.

O coletor faz paginação completa nos canais, pois a API de mensagens de canal
ordena cadeias de respostas e não oferece o mesmo filtro de data dos chats.
Equipes muito grandes podem exigir um coletor com fila para não exceder o tempo
do job. Há limites de 24 MB por XLSX, 250 mil células preenchidas por arquivo e
32 MB por lote de estado. Fontes fora desses limites são pendências, nunca
silenciosamente consideradas sincronizadas. Alterações feitas e desfeitas entre
duas verificações podem não aparecer: snapshots horários não são um histórico
de cada edição. Acesso delegado não inclui equipes compartilhadas em que a
titular não consta em `/me/joinedTeams`.

As novas tabelas têm RLS habilitada ao serem criadas em PostgreSQL e nenhuma
policy pública. O backend usa a conexão privilegiada já existente. Nenhum token
Microsoft é armazenado no banco. Backups atuais não incluem estas novas tabelas;
configurar backup do banco para manter o histórico externo antes de ativar em
produção. Não usar os backups parciais do aplicativo como única proteção.

Referências: [chats](https://learn.microsoft.com/en-us/graph/api/chat-list),
[mensagens de chat](https://learn.microsoft.com/en-us/graph/api/chat-list-messages),
[mensagens de canal](https://learn.microsoft.com/en-us/graph/api/channel-list-messages),
[conteúdo de arquivo](https://learn.microsoft.com/en-us/graph/api/driveitem-get-content),
[refresh tokens](https://learn.microsoft.com/en-us/entra/identity-platform/refresh-tokens).
