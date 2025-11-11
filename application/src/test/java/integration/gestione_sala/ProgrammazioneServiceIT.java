package integration.gestione_sala;

import integration.BaseIntegrationTest;
import it.unisa.application.sottosistemi.gestione_sala.service.ProgrammazioneService;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.time.LocalDate;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class ProgrammazioneServiceIT extends BaseIntegrationTest {

    private ProgrammazioneService service;

    @BeforeEach
    void setUp() throws SQLException {
        service = new ProgrammazioneService();

        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Mercogliano', 'Via Roma 1', 'Avellino', '83100');");
        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (2, 'Laquila', 'Via Firenze 2', 'L''Aquila', '67100');");

        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100);");
        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (2, 2, 1, 120);");

        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (1, 'Inception', 'Sci-Fi', 'T', 148, NULL, 'Thriller', TRUE);");
        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (2, 'Matrix', 'Azione', 'T', 136, NULL, 'VR action', TRUE);");

        execute("INSERT INTO slot (id, ora_inizio) VALUES (1, '18:00:00');");
        execute("INSERT INTO slot (id, ora_inizio) VALUES (2, '21:00:00');");
    }

    // ---------- Helper----------

    private int countProiezioni() throws SQLException {
        try (PreparedStatement ps = connection.prepareStatement("SELECT COUNT(*) FROM proiezione")) {
            try (ResultSet rs = ps.executeQuery()) {
                rs.next();
                return rs.getInt(1);
            }
        }
    }

    @RepeatedTest(5)
    void aggiungiProiezione_successo() throws Exception {
        int before = countProiezioni();

        int filmId = 1;
        int salaId = 1;
        List<Integer> slotIds = Arrays.asList(2, 1);
        LocalDate data = LocalDate.now().plusDays(1);

        boolean ok = service.aggiungiProiezione(filmId, salaId, slotIds, data);

        int after = countProiezioni();

        assertTrue(ok, "L'inserimento dovrebbe avere successo");
        assertEquals(before + 1, after, "Dovrebbe essere stata inserita una proiezione");
    }

    @RepeatedTest(5)
    void aggiungiProiezione_filmNonEsistente() throws Exception {
        int before = countProiezioni();

        int filmId = 999;      // non esiste
        int salaId = 1;        // esiste
        List<Integer> slotIds = Collections.singletonList(1);
        LocalDate data = LocalDate.now().plusDays(2);

        boolean ok = service.aggiungiProiezione(filmId, salaId, slotIds, data);

        int after = countProiezioni();

        assertFalse(ok, "Con film inesistente il metodo deve restituire false");
        assertEquals(before, after, "Non deve essere inserita alcuna proiezione");
    }

    @RepeatedTest(5)
    void aggiungiProiezione_filmNonInserito() throws Exception {
        execute("DELETE FROM film;");

        int before = countProiezioni();

        int filmId = 1;        // id valido in input ma la tabella film è vuota
        int salaId = 1;        // esiste
        List<Integer> slotIds = Collections.singletonList(1);
        LocalDate data = LocalDate.now().plusDays(3);

        boolean ok = service.aggiungiProiezione(filmId, salaId, slotIds, data);

        int after = countProiezioni();

        assertFalse(ok, "Senza film in tabella, deve fallire");
        assertEquals(before, after, "Non deve essere inserita alcuna proiezione");
    }

    @RepeatedTest(5)
    void aggiungiProiezione_dataPassata() throws Exception {
        int before = countProiezioni();

        int filmId = 1;        // esiste
        int salaId = 1;        // esiste
        List<Integer> slotIds = Collections.singletonList(1);
        LocalDate data = LocalDate.now().minusDays(1); // passata

        boolean ok = service.aggiungiProiezione(filmId, salaId, slotIds, data);

        int after = countProiezioni();

        assertFalse(ok, "Con data passata deve restituire false");
        assertEquals(before, after, "Non deve essere inserita alcuna proiezione");
    }

    @RepeatedTest(5)
    void aggiungiProiezione_dataNonInserita() throws Exception {
        int before = countProiezioni();

        int filmId = 1;        // esiste
        int salaId = 1;        // esiste
        List<Integer> slotIds = Collections.singletonList(1);
        LocalDate data = null; // nullo -> NPE

        boolean ok = service.aggiungiProiezione(filmId, salaId, slotIds, data);

        int after = countProiezioni();

        assertFalse(ok, "Con data nulla deve restituire false");
        assertEquals(before, after, "Non deve essere inserita alcuna proiezione");
    }

    @RepeatedTest(5)
    void aggiungiProiezione_slotNonDisponibile() throws Exception {
        int before = countProiezioni();

        int filmId = 1;        // esiste
        int salaId = 1;        // esiste
        List<Integer> slotIds = Collections.singletonList(999); // slot inesistente
        LocalDate data = LocalDate.now().plusDays(2);

        boolean ok = service.aggiungiProiezione(filmId, salaId, slotIds, data);

        int after = countProiezioni();

        assertFalse(ok, "Se nessuno slot selezionato è disponibile, deve restituire false");
        assertEquals(before, after, "Non deve essere inserita alcuna proiezione");
    }
}
