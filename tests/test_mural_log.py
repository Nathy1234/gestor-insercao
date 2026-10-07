import os
import tempfile
import unittest
from datetime import datetime
from pathlib import Path
from unittest.mock import patch

import openpyxl

_temporario = tempfile.TemporaryDirectory()
os.environ['DATABASE_URL'] = 'sqlite:///' + str(Path(_temporario.name) / 'teste.db')
os.environ['SECRET_KEY'] = 'chave-exclusiva-de-testes'
import app as gestor
from mural_log import diferencas_planilha, snapshot_planilha, validar_evento
from scripts.sincronizar_mural import evento_mensagem


class LogTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        gestor.app.config['TESTING'] = True
        with gestor.app.app_context():
            gestor.db.create_all()
        gestor._db_ready = True

    def setUp(self):
        self.env = patch.dict(os.environ, MURAL_SYNC_SECRET='s' * 40, MS_GRAPH_USER_ID='titular')
        self.env.start()
        self.client = gestor.app.test_client()
        self.headers = {'Authorization': 'Bearer ' + 's' * 40}
        with gestor.app.app_context():
            for model in (gestor.MuralEvento, gestor.MuralSyncState, gestor.MuralMensagem, gestor.AuditLog, gestor.User):
                gestor.db.session.query(model).delete()
            gestor.db.session.add(gestor.User(id=1, username='Equipe', password=gestor.hash_pw('senha-teste'), role='admin'))
            gestor.db.session.commit()

    def tearDown(self):
        self.env.stop()

    def evento(self, **campos):
        return dict(fonte='teams_grupo', chave='mensagem1', tipo_chat='group',
                    membros=['titular', 'colega1', 'colega2'], autor='Colega', origem='Grupo',
                    texto='<script>alert(1)</script>', ocorrido_em='2026-10-07T12:00:00-03:00', **campos)

    def post(self, eventos, estados=None):
        return self.client.post('/api/mural/sincronizacao', headers=self.headers,
                                json={'dono': 'titular', 'eventos': eventos, 'estados': estados or {}})

    def test_segredo_ausente_e_errado(self):
        self.assertEqual(self.client.get('/api/mural/sincronizacao').status_code, 401)
        with patch.dict(os.environ, MURAL_SYNC_SECRET=''):
            self.assertEqual(self.client.get('/api/mural/sincronizacao', headers=self.headers).status_code, 401)

    def test_nao_levar_conversa_dupla_nem_grupo_sem_titular(self):
        for campos in ({'tipo_chat': 'oneOnOne'}, {'membros': ['titular', 'colega']},
                       {'membros': ['um', 'dois', 'tres']}):
            e = self.evento()
            e.update(campos)
            self.assertEqual(self.post([e]).status_code, 400)
        with gestor.app.app_context():
            self.assertEqual(gestor.MuralEvento.query.count(), 0)

    def test_lote_invalido_nao_avanca_cursor(self):
        e = self.evento()
        e['membros'] = ['titular', 'colega']
        self.assertEqual(self.post([self.evento(), e], {'cursor': 'depois'}).status_code, 400)
        with gestor.app.app_context():
            self.assertEqual(gestor.MuralEvento.query.count(), 0)
            self.assertEqual(gestor.MuralSyncState.query.count(), 0)

    def test_reenvio_nao_duplica_e_checkpoint_persiste(self):
        self.assertEqual(self.post([self.evento()], {'cursor': 'novo'}).json['novos'], 1)
        self.assertEqual(self.post([self.evento()]).json['novos'], 0)
        self.assertEqual(self.client.get('/api/mural/sincronizacao', headers=self.headers).json['estados']['cursor'], 'novo')
        with gestor.app.app_context():
            self.assertEqual(gestor.MuralEvento.query.one().ocorrido_em, datetime(2026, 10, 7, 15))

    def test_log_escapa_conteudo_e_nao_expoe_privadas(self):
        self.post([self.evento()])
        with gestor.app.app_context():
            gestor.db.session.add(gestor.MuralMensagem(user_id=1, texto='SEGREDO PRIVADO', privada=True))
            gestor.db.session.add(gestor.AuditLog(username='Equipe', entity='user', action='senha', detail='NAO EXIBIR'))
            gestor.db.session.add(gestor.AuditLog(username='Equipe', entity='course', action='editar', detail='Curso atualizado'))
            gestor.db.session.commit()
        with self.client.session_transaction() as s:
            s['user_id'], s['username'], s['role'] = 1, 'Equipe', 'admin'
        resposta = self.client.get('/mural?aba=log')
        self.assertEqual(resposta.status_code, 200)
        html = resposta.get_data(as_text=True)
        self.assertIn('&lt;script&gt;', html)
        self.assertNotIn('Curso atualizado', html)
        self.assertNotIn('SEGREDO PRIVADO', html)
        self.assertNotIn('NAO EXIBIR', html)
        self.assertIn('💬 Mural', html)

    def test_acesso_ao_log_exige_login(self):
        self.assertEqual(self.client.get('/mural?aba=log').status_code, 302)

    def test_links_nao_executam_javascript(self):
        e = self.evento(link='javascript:alert(1)')
        self.assertEqual(validar_evento(e, 'titular')['link'], '')
        e['link'] = 'https://teams.microsoft.com.evil.example/path'
        self.assertEqual(validar_evento(e, 'titular')['link'], '')

    def test_todas_abas_inclusive_ocultas_e_sem_valores_no_estado(self):
        wb = openpyxl.Workbook()
        wb.active['A1'] = 'Curso que não está no Gestor'
        aba = wb.create_sheet('Oculta')
        aba.sheet_state = 'hidden'
        aba['B2'] = '=1+2'
        antes = snapshot_planilha(wb)
        self.assertEqual(diferencas_planilha(None, antes), [])
        self.assertNotIn('Curso que', str(antes))
        aba['B2'] = '=2+2'
        wb.create_sheet('Nova')
        depois = snapshot_planilha(wb)
        diferencas = '\n'.join(diferencas_planilha(antes, depois))
        self.assertIn('Oculta', diferencas)
        self.assertIn('B2', diferencas)
        self.assertIn('Aba adicionada: Nova', diferencas)
        self.assertEqual(diferencas_planilha(depois, depois), [])

    def test_mensagem_editada_e_excluida(self):
        msg = {'id': '1', 'messageType': 'message', 'createdDateTime': '2026-10-07T10:00:00Z',
               'lastModifiedDateTime': '2026-10-07T12:00:00Z', 'lastEditedDateTime': '2026-10-07T12:00:00Z',
               'body': {'content': '<p>Atualização</p>'}}
        e, _ = evento_mensagem(msg, {'id': 'grupo'}, '2026-10-07T11:00:00Z')
        self.assertIn('Mensagem editada', e['texto'])
        msg['deletedDateTime'] = '2026-10-07T12:00:00Z'
        e, _ = evento_mensagem(msg, {'id': 'grupo'}, '2026-10-07T11:00:00Z')
        self.assertIn('Mensagem excluída', e['texto'])
        self.assertNotIn('Atualização', e['texto'])


if __name__ == '__main__':
    unittest.main()
