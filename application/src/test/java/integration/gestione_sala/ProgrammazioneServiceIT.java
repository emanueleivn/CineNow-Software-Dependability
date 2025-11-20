package integration.gestione_sala;

import integration.BaseIT;
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

class ProgrammazioneServiceIT extends BaseIT {

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

    // ============================================
    // TEST POST MUTATION TESTING
    // ============================================

    // Boundary case: data oggi
    @RepeatedTest(5)
    void aggiungiProiezione_dataOggi_success() throws Exception {
        int before = countProiezioni();
        int filmId = 1;
        int salaId = 1;
        List<Integer> slotIds = Collections.singletonList(1);
        LocalDate oggi = LocalDate.now(); // Boundary case: oggi stesso

        boolean ok = service.aggiungiProiezione(filmId, salaId, slotIds, oggi);

        int after = countProiezioni();

        assertTrue(ok, "La data di oggi deve essere accettata");
        assertEquals(before + 1, after, "Deve essere inserita una proiezione per oggi");
    }

    @RepeatedTest(5)
    void aggiungiProiezione_salaNonEsistente() throws Exception {
        // AGGIUNGI questa verifica
        execute("DELETE FROM sala WHERE id = 999;"); // Assicura che non esista

        int before = countProiezioni();
        int filmId = 1;
        int salaId = 999;      // NON esiste garantito
        List<Integer> slotIds = Collections.singletonList(1);
        LocalDate data = LocalDate.now().plusDays(1);

        boolean ok = service.aggiungiProiezione(filmId, salaId, slotIds, data);

        assertFalse(ok, "Con sala inesistente deve restituire false");
        assertEquals(before, countProiezioni());
    }

    @RepeatedTest(5)
    void aggiungiProiezione_slotListaVuota() throws Exception {
        int before = countProiezioni();

        List<Integer> slotIds = Arrays.asList(999, 888, 777);
        LocalDate data = LocalDate.now().plusDays(1);

        boolean ok = service.aggiungiProiezione(1, 1, slotIds, data);

        assertFalse(ok, "Con tutti slot invalidi → lista vuota → deve fallire");
        assertEquals(before, countProiezioni());
    }

    @RepeatedTest(5)
    void aggiungiProiezione_multiploSlotOrdinamento() throws Exception {
        // UCCIDE: mutazioni sul sorting (linee 77-81)
        int before = countProiezioni();

        int filmId = 1;
        int salaId = 1;
        // Slot in ordine inverso per testare il sorting
        List<Integer> slotIds = Arrays.asList(2, 1); // 21:00, 18:00
        LocalDate data = LocalDate.now().plusDays(1);

        boolean ok = service.aggiungiProiezione(filmId, salaId, slotIds, data);

        int after = countProiezioni();

        assertTrue(ok, "Deve gestire correttamente l'ordinamento degli slot");
        assertEquals(before + 1, after, "Deve essere inserita una proiezione");

        // Verifica che sia stato usato il primo slot DOPO l'ordinamento (slot 1 - 18:00)
        try (PreparedStatement ps = connection.prepareStatement(
                "SELECT id_orario FROM proiezione ORDER BY id DESC LIMIT 1")) {
            try (ResultSet rs = ps.executeQuery()) {
                assertTrue(rs.next());
                assertEquals(1, rs.getInt("id_orario"),
                        "Deve usare lo slot con orario più basso (dopo ordinamento)");
            }
        }
    }

    @RepeatedTest(5)
    void aggiungiProiezione_slotParzialmenteValidi() throws Exception {
        int before = countProiezioni();

        int filmId = 1;
        int salaId = 1;
        // Mix di slot validi (1, 2) e invalidi (999)
        List<Integer> slotIds = Arrays.asList(1, 999, 2);
        LocalDate data = LocalDate.now().plusDays(1);

        boolean ok = service.aggiungiProiezione(filmId, salaId, slotIds, data);

        int after = countProiezioni();

        assertTrue(ok, "Deve accettare anche se alcuni slot non esistono (usa solo quelli validi)");
        assertEquals(before + 1, after, "Deve essere inserita una proiezione");
    }

    @RepeatedTest(5)
    void aggiungiProiezione_filmNullDaDAO() throws Exception {
        execute("DELETE FROM film WHERE id = 1;");

        int before = countProiezioni();

        boolean ok = service.aggiungiProiezione(1, 1, Arrays.asList(1), LocalDate.now().plusDays(1));

        assertFalse(ok, "Con film null dal DAO deve restituire false");
        assertEquals(before, countProiezioni(), "Non deve inserire proiezioni");
    }

    @RepeatedTest(5)
    void aggiungiProiezione_daoFallisceRestituisceFalse() throws Exception {
        // Forza il DAO a fallire causando violazione vincolo FK
        execute("DELETE FROM sala;");
        execute("DELETE FROM film;");

        int before = countProiezioni();

        // Film e sala non esistono → DAO.create() deve restituire false
        boolean ok = service.aggiungiProiezione(1, 1, Arrays.asList(1), LocalDate.now().plusDays(1));

        assertFalse(ok, "Se DAO.create() fallisce, aggiungiProiezione deve restituire false");
        assertEquals(before, countProiezioni());
    }

    // UCCIDE: mutazione sul catch block generico
    @RepeatedTest(5)
    void aggiungiProiezione_eccezioneGenerica() throws Exception {
        int before = countProiezioni();
        execute("DELETE FROM sala WHERE id = 1;");

        int filmId = 1;
        int salaId = 1; // La sala non esiste più nel DB
        List<Integer> slotIds = Collections.singletonList(1);
        LocalDate data = LocalDate.now().plusDays(1);

        boolean ok = service.aggiungiProiezione(filmId, salaId, slotIds, data);

        int after = countProiezioni();

        assertFalse(ok, "Deve restituire false in caso di eccezione SQL");
        assertEquals(before, after, "Non deve essere inserita alcuna proiezione");
    }

    @RepeatedTest(5)
    void aggiungiProiezione_slotNonOrdinatiUsaPrimo() throws Exception {
        int before = countProiezioni();

        // Passa slot in ordine INVERSO: prima 2 (21:00), poi 1 (18:00)
        List<Integer> slotIds = Arrays.asList(2, 1);
        LocalDate data = LocalDate.now().plusDays(1);

        boolean ok = service.aggiungiProiezione(1, 1, slotIds, data);

        assertTrue(ok);
        assertEquals(before + 1, countProiezioni());

        // VERIFICA CRUCIALE: deve usare lo slot 1 (18:00), non il 2
        try (PreparedStatement ps = connection.prepareStatement(
                "SELECT id_orario FROM proiezione WHERE id = (SELECT MAX(id) FROM proiezione)")) {
            try (ResultSet rs = ps.executeQuery()) {
                assertTrue(rs.next());
                // Se il sorting NON funziona, userebbe slot 2 (primo della lista)
                // Con sorting funzionante, usa slot 1 (più basso dopo ordinamento)
                assertEquals(1, rs.getInt("id_orario"),
                        "DEVE usare lo slot con orario MINORE dopo ordinamento (18:00)");
            }
        }
    }

    // TEST POST MUTATION TESTING- Sorting algorithm
    @RepeatedTest(5)
    void aggiungiProiezione_treSlotDisordinati() throws Exception {
        // Aggiungi un terzo slot
        execute("INSERT INTO slot (id, ora_inizio) VALUES (3, '15:00:00');");

        int before = countProiezioni();

        // Passa slot completamente disordinati: 2 (21:00), 1 (18:00), 3 (15:00)
        List<Integer> slotIds = Arrays.asList(2, 1, 3);
        LocalDate data = LocalDate.now().plusDays(1);

        boolean ok = service.aggiungiProiezione(1, 1, slotIds, data);

        assertTrue(ok);
        assertEquals(before + 1, countProiezioni());

        // Verifica che usi lo slot 3 (15:00), il più basso
        try (PreparedStatement ps = connection.prepareStatement(
                "SELECT id_orario FROM proiezione WHERE id = (SELECT MAX(id) FROM proiezione)")) {
            try (ResultSet rs = ps.executeQuery()) {
                assertTrue(rs.next());
                assertEquals(3, rs.getInt("id_orario"),
                        "Con sorting corretto deve usare lo slot 3 (15:00)");
            }
        }
    }

    @RepeatedTest(5)
    void aggiungiProiezione_slotGiaOrdinatiNonCambiano() throws Exception {
        int before = countProiezioni();

        // Slot già in ordine crescente
        List<Integer> slotIds = Arrays.asList(1, 2); // 18:00, 21:00
        LocalDate data = LocalDate.now().plusDays(1);

        boolean ok = service.aggiungiProiezione(1, 1, slotIds, data);

        assertTrue(ok);

        // Deve comunque usare il primo (già corretto)
        try (PreparedStatement ps = connection.prepareStatement(
                "SELECT id_orario FROM proiezione WHERE id = (SELECT MAX(id) FROM proiezione)")) {
            try (ResultSet rs = ps.executeQuery()) {
                assertTrue(rs.next());
                assertEquals(1, rs.getInt("id_orario"));
            }
        }
    }

    @RepeatedTest(5)
    void aggiungiProiezione_unSoloSlot_noSorting() throws Exception {
        // Edge case: un solo slot → sorting non fa nulla
        int before = countProiezioni();

        List<Integer> slotIds = Collections.singletonList(2);
        LocalDate data = LocalDate.now().plusDays(1);

        boolean ok = service.aggiungiProiezione(1, 1, slotIds, data);

        assertTrue(ok);
        assertEquals(before + 1, countProiezioni());

        // Deve usare l'unico slot disponibile
        try (PreparedStatement ps = connection.prepareStatement(
                "SELECT id_orario FROM proiezione WHERE id = (SELECT MAX(id) FROM proiezione)")) {
            try (ResultSet rs = ps.executeQuery()) {
                assertTrue(rs.next());
                assertEquals(2, rs.getInt("id_orario"));
            }
        }
    }
}
