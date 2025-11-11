package integration.gestione_prenotazione;

import integration.BaseIntegrationTest;
import it.unisa.application.model.entity.*;
import it.unisa.application.sottosistemi.gestione_prenotazione.service.PrenotazioneService;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class PrenotazioneServiceIT extends BaseIntegrationTest {

    private PrenotazioneService service;
    private Cliente cliente;
    private Proiezione proiezione;
    private List<PostoProiezione> postiDisponibili;

    @BeforeEach
    void setup() throws SQLException {
        service = new PrenotazioneService();

        execute("INSERT INTO utente (email, password, ruolo) VALUES ('cliente@email.com', 'HASHED_pw', 'cliente');");
        execute("INSERT INTO cliente (email, nome, cognome) VALUES ('cliente@email.com', 'Mario', 'Rossi');");

        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Cinema Centro', 'Via Roma 10', 'Avellino', '83100');");
        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100);");
        execute("INSERT INTO slot (id, ora_inizio) VALUES (1, '18:00:00');");
        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (1, 'Inception', 'Sci-Fi', 'T', 148, NULL, 'Thriller', TRUE);");
        execute("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) " +
                "VALUES (1, CURRENT_DATE, 1, 1, 1);");

        execute("INSERT INTO posto (id_sala, fila, numero) VALUES (1, 'A', 1);");
        execute("INSERT INTO posto (id_sala, fila, numero) VALUES (1, 'A', 2);");
        execute("INSERT INTO posto (id_sala, fila, numero) VALUES (1, 'A', 3);");

        // Posti proiezione disponibili
        execute("INSERT INTO posto_proiezione (id_sala, fila, numero, id_proiezione, stato) VALUES (1, 'A', 1, 1, TRUE);");
        execute("INSERT INTO posto_proiezione (id_sala, fila, numero, id_proiezione, stato) VALUES (1, 'A', 2, 1, TRUE);");
        execute("INSERT INTO posto_proiezione (id_sala, fila, numero, id_proiezione, stato) VALUES (1, 'A', 3, 1, TRUE);");

        cliente = new Cliente("cliente@email.com", "HASHED_pw", "cliente", "Rossi");
        Film film = new Film(1, "Inception", "Sci-Fi", "T", 148, null, "Thriller", true);
        Sala sala = new Sala(1, 1, 100, null);
        Slot slot = new Slot(1, java.sql.Time.valueOf("18:00:00"));
        proiezione = new Proiezione(1, sala, film, LocalDate.now(), slot);

        postiDisponibili = new ArrayList<>();
        postiDisponibili.add(new PostoProiezione(sala, 'A', 1, proiezione));
        postiDisponibili.add(new PostoProiezione(sala, 'A', 2, proiezione));
    }

    // ============================================
    // TEST CASO POSITIVO
    // ============================================

    @RepeatedTest(5)
    void aggiungiOrdine_successo() throws SQLException {
        service.aggiungiOrdine(cliente, postiDisponibili, proiezione);

        // Verifica che sia stata creata la prenotazione
        try (ResultSet rs = connection.createStatement().executeQuery("SELECT COUNT(*) AS cnt FROM prenotazione")) {
            assertTrue(rs.next());
            assertEquals(1, rs.getInt("cnt"), "Deve esistere una prenotazione");
        }

        // Verifica che i posti siano stati occupati
        try (ResultSet rs = connection.createStatement().executeQuery(
                "SELECT COUNT(*) AS cnt FROM occupa")) {
            assertTrue(rs.next());
            assertEquals(2, rs.getInt("cnt"), "Devono essere occupati due posti");
        }
    }

    // ============================================
    // TEST CASI DI ERRORE
    // ============================================

    @RepeatedTest(5)
    void aggiungiOrdine_clienteNull() {
        assertThrows(IllegalArgumentException.class, () ->
                service.aggiungiOrdine(null, postiDisponibili, proiezione));

    }

    @RepeatedTest(5)
    void aggiungiOrdine_postiNull() {
        assertThrows(IllegalArgumentException.class, () ->
                service.aggiungiOrdine(cliente, null, proiezione));
    }

    @RepeatedTest(5)
    void aggiungiOrdine_postiVuoti() {
        assertThrows(IllegalArgumentException.class, () ->
                service.aggiungiOrdine(cliente, new ArrayList<>(), proiezione));
    }

    @RepeatedTest(5)
    void aggiungiOrdine_proiezioneNull() {
        assertThrows(IllegalArgumentException.class, () ->
                service.aggiungiOrdine(cliente, postiDisponibili, null));
    }

    @RepeatedTest(5)
    void aggiungiOrdine_postoOccupato() {
        // Segna un posto come già occupato
        postiDisponibili.getFirst().setStato(false);

        assertThrows(IllegalArgumentException.class, () ->
                service.aggiungiOrdine(cliente, postiDisponibili, proiezione));
    }

    // ============================================
    // TEST METODO ottieniPostiProiezione()
    // ============================================

    @RepeatedTest(5)
    void ottieniPostiProiezione_successo() {
        List<PostoProiezione> result = service.ottieniPostiProiezione(proiezione);
        assertNotNull(result);
        assertFalse(result.isEmpty(), "La lista dei posti non deve essere vuota");
    }
}
