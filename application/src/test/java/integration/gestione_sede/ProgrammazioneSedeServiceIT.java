package integration.gestione_sede;

import integration.BaseIntegrationTest;
import it.unisa.application.model.entity.Film;
import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.model.entity.Sede;
import it.unisa.application.sottosistemi.gestione_sede.service.ProgrammazioneSedeService;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import java.sql.SQLException;
import java.time.LocalDate;
import java.util.List;
import java.util.Objects;

import static org.junit.jupiter.api.Assertions.*;

public class ProgrammazioneSedeServiceIT extends BaseIntegrationTest {

    private ProgrammazioneSedeService service;

    @BeforeEach
    void setup() throws SQLException {
        service = new ProgrammazioneSedeService();

        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Cinema Centrale', 'Via Roma 10', 'Napoli', '80100');");

        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (1, 'Inception', 'Sci-Fi', 'T', 148, NULL, 'Thriller fantascientifico', TRUE);");
        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (2, 'Matrix', 'Azione', 'T', 136, NULL, 'Azione e realtà virtuale', TRUE);");

        execute("INSERT INTO slot (id, ora_inizio) VALUES (1, '18:00:00');");
        execute("INSERT INTO slot (id, ora_inizio) VALUES (2, '21:00:00');");

        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100);");

        LocalDate today = LocalDate.now();
        LocalDate tomorrow = today.plusDays(1);
        LocalDate nextWeek = today.plusDays(6);

        execute(String.format("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) VALUES (1, DATE '%s', 1, 1, 1);", today));
        execute(String.format("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) VALUES (2, DATE '%s', 1, 1, 2);", tomorrow));
        execute(String.format("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) VALUES (3, DATE '%s', 2, 1, 1);", nextWeek));
    }

    @RepeatedTest(5)
    void testGetProgrammazione_restituisceSoloProiezioniFuture() {
        List<Proiezione> programmazione = service.getProgrammazione(1);

        assertNotNull(programmazione);
        assertFalse(programmazione.isEmpty());
        assertTrue(programmazione.stream().noneMatch(p ->
                p.getDataProiezione().isBefore(LocalDate.now())
        ));

        for (int i = 1; i < programmazione.size(); i++) {
            LocalDate prevDate = programmazione.get(i - 1).getDataProiezione();
            LocalDate currDate = programmazione.get(i).getDataProiezione();
            assertFalse(currDate.isBefore(prevDate));
        }
    }

    @RepeatedTest(5)
    void testGetProiezioniFilm_restituisceSoloSettimanaCorrente() {
        List<Proiezione> proiezioni = service.getProiezioniFilm(1, 1);

        assertNotNull(proiezioni);
        assertTrue(proiezioni.stream().allMatch(p ->
                !p.getDataProiezione().isBefore(LocalDate.now()) &&
                        !p.getDataProiezione().isAfter(LocalDate.now().plusDays(7))
        ));

        assertTrue(proiezioni.stream().allMatch(p -> p.getFilmProiezione().getId() == 1));
    }

    @RepeatedTest(5)
    void testGetCatalogoSede_restituisceFilmAssociati() {
        Sede sede = new Sede(1);
        List<Film> catalogo = service.getCatalogoSede(sede);

        assertNotNull(catalogo);
        assertFalse(catalogo.isEmpty());
        assertTrue(catalogo.stream().allMatch(Objects::nonNull));
    }

    @RepeatedTest(5)
    void testGetProgrammazione_sedeVuota() throws SQLException {
        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (99, 'Cinema Vuoto', 'Via Test 1', 'Roma', '00100');");

        List<Proiezione> programmazione = service.getProgrammazione(99);
        assertNotNull(programmazione);
        assertTrue(programmazione.isEmpty());
    }
}
