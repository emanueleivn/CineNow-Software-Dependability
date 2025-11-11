package integration.gestione_sala;

import integration.BaseIntegrationTest;
import it.unisa.application.sottosistemi.gestione_sala.service.SlotService;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import java.sql.SQLException;
import java.time.LocalDate;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

class SlotServiceIT extends BaseIntegrationTest {

    private SlotService service;

    @BeforeEach
    void setUp() throws SQLException {
        service = new SlotService();

        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Mercogliano', 'Via Roma 1', 'Avellino', '83100');");
        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100);");

        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (1, 'Inception', 'Sci-Fi', 'T', 148, NULL, 'Thriller', TRUE);");
        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (2, 'Matrix', 'Azione', 'T', 136, NULL, 'Azione virtuale', TRUE);");

        execute("INSERT INTO slot (id, ora_inizio) VALUES (1, '18:00:00');");
        execute("INSERT INTO slot (id, ora_inizio) VALUES (2, '21:00:00');");
        execute("INSERT INTO slot (id, ora_inizio) VALUES (3, '23:00:00');");
    }

    // ===================================
    // TEST CASO POSITIVO
    // ===================================

    @RepeatedTest(5)
    void slotDisponibili_successo() throws Exception {
        LocalDate inizio = LocalDate.now().plusDays(1);
        LocalDate fine = inizio.plusDays(2);

        Map<String, Object> result = service.slotDisponibili(1, 1, inizio, fine);

        assertNotNull(result, "Il risultato non deve essere nullo");
        assertTrue(result.containsKey("durataFilm"));
        assertEquals(148, result.get("durataFilm"), "La durata del film deve essere corretta");

        List<Map<String, Object>> calendario = (List<Map<String, Object>>) result.get("calendar");
        assertEquals(3, calendario.size(), "Devono esserci 3 giorni di calendario (inizio, +1, +2)");

        for (Map<String, Object> giorno : calendario) {
            assertTrue(giorno.containsKey("data"));
            assertTrue(giorno.containsKey("slots"));
            List<Map<String, Object>> slots = (List<Map<String, Object>>) giorno.get("slots");
            assertFalse(slots.isEmpty(), "Ogni giorno deve avere slot disponibili");
        }
    }

    // ===================================
    // TEST CASI DI ERRORE
    // ===================================

    @RepeatedTest(5)
    void slotDisponibili_filmNonEsistente() {
        LocalDate inizio = LocalDate.now().plusDays(1);
        LocalDate fine = inizio.plusDays(1);
        assertThrows(RuntimeException.class, () ->
                service.slotDisponibili(999, 1, inizio, fine));

    }

    @RepeatedTest(5)
    void slotDisponibili_dataInvalida() throws Exception {
        LocalDate inizio = LocalDate.now().plusDays(5);
        LocalDate fine = LocalDate.now().plusDays(1); // data fine precedente

        // Il ciclo while non itera (current.isAfter(dataFine)), ma non genera eccezione → mappa vuota
        Map<String, Object> result = service.slotDisponibili(1, 1, inizio, fine);

        assertTrue(((List<?>) result.get("calendar")).isEmpty(), "Il calendario deve essere vuoto se l'intervallo è invalido");
    }

    @RepeatedTest(5)
    void slotDisponibili_slotOccupato() throws Exception {
        LocalDate oggi = LocalDate.now().plusDays(1);

        execute("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) VALUES (1, '" + oggi + "', 2, 1, 1);");

        Map<String, Object> result = service.slotDisponibili(1, 1, oggi, oggi);

        List<Map<String, Object>> calendario = (List<Map<String, Object>>) result.get("calendar");
        List<Map<String, Object>> slots = (List<Map<String, Object>>) calendario.get(0).get("slots");

        boolean almenoUnoOccupato = slots.stream().anyMatch(s -> (boolean) s.get("occupato"));
        assertTrue(almenoUnoOccupato, "Almeno uno slot deve risultare occupato");
    }

    @RepeatedTest(5)
    void slotDisponibili_nessunoSlotDisponibile() throws Exception {
        execute("DELETE FROM slot;");

        LocalDate data = LocalDate.now().plusDays(1);

        assertThrows(Exception.class, () ->
                service.slotDisponibili(1, 1, data, data));
    }
}
