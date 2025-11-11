package integration.gestione_utente;

import integration.BaseIntegrationTest;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.sottosistemi.gestione_utente.service.RegistrazioneService;
import it.unisa.application.utilities.PasswordHash;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.RepeatedTest;
import org.mockito.MockedStatic;

import java.sql.ResultSet;
import java.sql.SQLException;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.mockStatic;

class RegistrazioneServiceIT extends BaseIntegrationTest {

    private RegistrazioneService service;

    @BeforeEach
    void setUp() {
        service = new RegistrazioneService();
    }

    @RepeatedTest(5)
    @DisplayName("Email nel formato non corretto → registrazione fallisce")
    void registrazione_emailFormatoErrato() {
        Cliente result = service.registrazione(
                "email-senza-chiocciola",
                "Password123!",
                "Mario",
                "Rossi"
        );
        assertNull(result, "Email nel formato errato deve restituire null");
    }

    @RepeatedTest(5)
    @DisplayName("Email già esistente → registrazione fallisce")
    void registrazione_emailGiaEsistente() throws SQLException {
        execute("INSERT INTO utente (email, password, ruolo) VALUES ('gia@email.com', 'HASHED_pw', 'cliente')");
        execute("INSERT INTO cliente (email, nome, cognome) VALUES ('gia@email.com', 'Luca', 'Bianchi')");

        Cliente result = service.registrazione(
                "gia@email.com",
                "Password123!",
                "Mario",
                "Rossi"
        );
        assertNull(result, "Registrazione con email già esistente deve restituire null");
    }

    @RepeatedTest(5)
    @DisplayName("Email vuota → registrazione fallisce")
    void registrazione_emailVuota() {
        Cliente result = service.registrazione(
                "",
                "Password123!",
                "Mario",
                "Rossi"
        );
        assertNull(result, "Registrazione con email vuota deve restituire null");
    }

    @RepeatedTest(5)
    @DisplayName("Password troppo corta o non valida → registrazione fallisce")
    void registrazione_passwordNonValida() {
        Cliente result = service.registrazione(
                "test@email.com",
                "abc",
                "Mario",
                "Rossi"
        );
        assertNull(result, "Password non valida deve restituire null");
    }

    @RepeatedTest(5)
    @DisplayName("Password mancante → registrazione fallisce")
    void registrazione_passwordMancante() {
        Cliente result = service.registrazione(
                "utente@email.com",
                "",
                "Mario",
                "Rossi"
        );
        assertNull(result, "Password mancante deve restituire null");
    }

    @RepeatedTest(5)
    @DisplayName("Nome nel formato non valido → registrazione fallisce")
    void registrazione_nomeNonValido() {
        Cliente result = service.registrazione(
                "utente@email.com",
                "Password123!",
                "M4r10",
                "Rossi"
        );
        assertNull(result, "Nome non valido deve restituire null");
    }

    @RepeatedTest(5)
    @DisplayName("Nome mancante → registrazione fallisce")
    void registrazione_nomeMancante() {
        Cliente result = service.registrazione(
                "utente@email.com",
                "Password123!",
                "",
                "Rossi"
        );
        assertNull(result, "Nome mancante deve restituire null");
    }

    @RepeatedTest(5)
    @DisplayName("Cognome nel formato non valido → registrazione fallisce")
    void registrazione_cognomeNonValido() {
        Cliente result = service.registrazione(
                "utente@email.com",
                "Password123!",
                "Mario",
                "R0$$i"
        );
        assertNull(result, "Cognome non valido deve restituire null");
    }

    @RepeatedTest(5)
    @DisplayName("Cognome mancante → registrazione fallisce")
    void registrazione_cognomeMancante() {
        Cliente result = service.registrazione(
                "utente@email.com",
                "Password123!",
                "Mario",
                ""
        );
        assertNull(result, "Cognome mancante deve restituire null");
    }

    @RepeatedTest(5)
    @DisplayName("Registrazione valida → Cliente creato e salvato nel DB")
    void registrazione_valida_ok() throws SQLException {
        try (MockedStatic<PasswordHash> mock = mockStatic(PasswordHash.class)) {
            mock.when(() -> PasswordHash.hash("Password123!")).thenReturn("HASHED_pw");

            Cliente result = service.registrazione(
                    "nuovo@email.com",
                    "Password123!",
                    "Mario",
                    "Rossi"
            );

            assertNotNull(result, "Registrazione valida deve restituire un Cliente");
            assertEquals("nuovo@email.com", result.getEmail());
            assertEquals("Mario", result.getNome());
            assertEquals("Rossi", result.getCognome());

            try (var stmt = connection.prepareStatement("SELECT * FROM utente WHERE email=?")) {
                stmt.setString(1, "nuovo@email.com");
                ResultSet rs = stmt.executeQuery();
                assertTrue(rs.next(), "L'utente deve essere salvato nel DB");
                assertEquals("HASHED_pw", rs.getString("password"));
                assertEquals("cliente", rs.getString("ruolo"));
            }
        }
    }
}
