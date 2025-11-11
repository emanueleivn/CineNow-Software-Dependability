package integration.gestione_utente;

import integration.BaseIntegrationTest;
import it.unisa.application.model.entity.GestoreSede;
import it.unisa.application.model.entity.Utente;
import it.unisa.application.sottosistemi.gestione_utente.service.AutenticazioneService;
import it.unisa.application.utilities.PasswordHash;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;
import org.mockito.MockedStatic;

import java.sql.SQLException;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.mockStatic;

class AutenticazioneServiceIT extends BaseIntegrationTest {

    private AutenticazioneService service;

    @BeforeEach
    void setUp() {
        service = new AutenticazioneService();
    }

    @RepeatedTest(5)
    void loginCliente_ok() throws SQLException {
        execute("INSERT INTO utente (email, password, ruolo) VALUES ('cliente1@email.com', 'HASHED_password1', 'cliente')");
        execute("INSERT INTO cliente (email, nome, cognome) VALUES ('cliente1@email.com', 'Mario', 'Rossi')");

        try (MockedStatic<PasswordHash> mock = mockStatic(PasswordHash.class)) {
            mock.when(() -> PasswordHash.hash("password1")).thenReturn("HASHED_password1");

            Utente result = service.login("cliente1@email.com", "password1");

            assertNotNull(result, "L'utente non dovrebbe essere nullo");
            assertEquals("cliente", result.getRuolo(), "Il ruolo deve essere 'cliente'");
        }
    }

    @RepeatedTest(5)
    void loginGestore_ok() throws SQLException {
        execute("INSERT INTO utente (email, password, ruolo) VALUES ('gestore@example.com', 'HASHED_gestore', 'gestore_sede')");
        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Cinema Centro', 'Via Roma 1', 'Napoli', '80100')");
        execute("INSERT INTO gest_sede (email, id_sede) VALUES ('gestore@example.com', 1)");

        try (MockedStatic<PasswordHash> mock = mockStatic(PasswordHash.class)) {
            mock.when(() -> PasswordHash.hash("gestore")).thenReturn("HASHED_gestore");

            Utente result = service.login("gestore@example.com", "gestore");

            assertNotNull(result, "Il gestore non dovrebbe essere nullo");
            assertInstanceOf(GestoreSede.class, result, "Il risultato deve essere un GestoreSede");
            assertEquals("Cinema Centro", ((GestoreSede) result).getSede().getNome(),
                    "Il nome della sede deve corrispondere a 'Cinema Centro'");
        }
    }

    @RepeatedTest(5)
    void login_emailNonEsistente_restituisceNull() {
        try (MockedStatic<PasswordHash> mock = mockStatic(PasswordHash.class)) {
            mock.when(() -> PasswordHash.hash("qualunque")).thenReturn("HASHED_irrelevante");

            Utente result = service.login("inesistente@email.com", "qualunque");
            assertNull(result, "Il login di un'email inesistente deve restituire null");
        }
    }

    @RepeatedTest(5)
    void login_passwordErrata_restituisceNull() throws SQLException {
        execute("INSERT INTO utente (email, password, ruolo) VALUES ('utente@errato.com', 'HASHED_password_corretta', 'cliente')");

        try (MockedStatic<PasswordHash> mock = mockStatic(PasswordHash.class)) {
            mock.when(() -> PasswordHash.hash("sbagliata")).thenReturn("HASHED_password_sbagliata");

            Utente result = service.login("utente@errato.com", "sbagliata");
            assertNull(result, "Il login con password errata deve restituire null");
        }
    }
}
