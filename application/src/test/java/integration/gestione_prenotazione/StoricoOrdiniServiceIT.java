package integration.gestione_prenotazione;

import integration.BaseIntegrationTest;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.model.entity.Prenotazione;
import it.unisa.application.sottosistemi.gestione_prenotazione.service.StoricoOrdiniService;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class StoricoOrdiniServiceIT extends BaseIntegrationTest {

    private StoricoOrdiniService service;
    private Cliente clienteConOrdini;
    private Cliente clienteSenzaOrdini;

    @BeforeEach
    void setup() throws SQLException {
        service = new StoricoOrdiniService();

        execute("INSERT INTO utente (email, password, ruolo) VALUES ('cliente1@email.com', 'HASHED_pw', 'cliente');");
        execute("INSERT INTO cliente (email, nome, cognome) VALUES ('cliente1@email.com', 'Mario', 'Rossi');");

        execute("INSERT INTO utente (email, password, ruolo) VALUES ('cliente2@email.com', 'HASHED_pw', 'cliente');");
        execute("INSERT INTO cliente (email, nome, cognome) VALUES ('cliente2@email.com', 'Luca', 'Bianchi');");

        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Cinema Centrale', 'Via Roma 10', 'Napoli', '80100');");
        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 120);");
        execute("INSERT INTO slot (id, ora_inizio) VALUES (1, '18:00:00');");
        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (1, 'Inception', 'Sci-Fi', 'T', 148, NULL, 'Thriller', TRUE);");
        execute("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) " +
                "VALUES (1, CURRENT_DATE, 1, 1, 1);");

        execute("INSERT INTO prenotazione (id, email_cliente, id_proiezione) VALUES (1, 'cliente1@email.com', 1);");
        execute("INSERT INTO prenotazione (id, email_cliente, id_proiezione) VALUES (2, 'cliente1@email.com', 1);");

        clienteConOrdini = new Cliente("cliente1@email.com", "HASHED_pw", "Mario", "Rossi");
        clienteSenzaOrdini = new Cliente("cliente2@email.com", "HASHED_pw", "Luca", "Bianchi");
    }

    @RepeatedTest(5)
    void storicoOrdini_clienteConOrdini() throws SQLException {
        List<Prenotazione> ordini = service.storicoOrdini(clienteConOrdini);

        assertNotNull(ordini, "La lista non deve essere null");
        assertEquals(2, ordini.size(), "Il cliente deve avere due ordini");

        try (ResultSet rs = connection.createStatement().executeQuery(
                "SELECT COUNT(*) AS cnt FROM prenotazione WHERE email_cliente = 'cliente1@email.com'")) {
            rs.next();
            assertEquals(2, rs.getInt("cnt"));
        }
    }

    @RepeatedTest(5)
    void storicoOrdini_clienteSenzaOrdini() {
        List<Prenotazione> ordini = service.storicoOrdini(clienteSenzaOrdini);

        assertNotNull(ordini, "La lista non deve essere null anche se vuota");
        assertTrue(ordini.isEmpty(), "Il cliente non deve avere ordini");
    }

    @RepeatedTest(5)
    void storicoOrdini_clienteNull() {
        assertThrows(IllegalArgumentException.class, () ->
                service.storicoOrdini(null));
    }
}
