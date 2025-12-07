package benchmark;

import it.unisa.application.model.dao.FilmDAO;
import it.unisa.application.model.dao.ProiezioneDAO;
import it.unisa.application.model.dao.SalaDAO;
import it.unisa.application.model.dao.SlotDAO;
import it.unisa.application.model.entity.*;
import it.unisa.application.sottosistemi.gestione_sala.service.ProgrammazioneService;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.sql.Time;
import java.time.LocalDate;
import java.time.LocalTime;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.mockito.Mockito.*;

/**
 * Benchmark per ProgrammazioneService.aggiungiProiezione()
 * Testa aggiunta di proiezioni con vari casi.
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 15, time = 1)
@Measurement(iterations = 40, time = 1)
public class ProgrammazioneServiceBenchmark {

    @State(Scope.Benchmark)
    public static class ProgrammazioneState {
        public ProgrammazioneService programmazioneService;
        public Film testFilm;
        public Sala testSala;
        public List<Integer> fewSlotIds;
        public List<Integer> manySlotIds;
        public LocalDate testDate;

        @Setup
        public void setup() {
            FilmDAO filmDAOMock = mock(FilmDAO.class);
            SalaDAO salaDAOMock = mock(SalaDAO.class);
            SlotDAO slotDAOMock = mock(SlotDAO.class);
            ProiezioneDAO proiezioneDAOMock = mock(ProiezioneDAO.class);

            testFilm = new Film(1, "Test Film", "Drammatico", "PG-13",
                    120, new byte[0], "Test", true);
            testSala = new Sala(1, 1, 100, new Sede(1, "Test Sede", "Via Test"));

            when(filmDAOMock.retrieveById(1)).thenReturn(testFilm);
            when(filmDAOMock.retrieveById(999)).thenReturn(null);
            when(salaDAOMock.retrieveById(1)).thenReturn(testSala);
            when(salaDAOMock.retrieveById(999)).thenReturn(null);

            List<Slot> slots = new ArrayList<>();
            for (int i = 1; i <= 8; i++) {
                LocalTime startTime = LocalTime.of(9 + (i - 1) / 2,
                        (i - 1) % 2 == 0 ? 0 : 30);
                slots.add(new Slot(i, Time.valueOf(startTime)));
            }
            when(slotDAOMock.retrieveAllSlots()).thenReturn(slots);
            when(proiezioneDAOMock.create(any())).thenReturn(true);

            programmazioneService = mock(ProgrammazioneService.class, CALLS_REAL_METHODS);
            injectDAOs(programmazioneService, filmDAOMock, salaDAOMock, slotDAOMock, proiezioneDAOMock);

            fewSlotIds = Arrays.asList(1, 2);
            manySlotIds = new ArrayList<>();
            for (int i = 1; i <= 8; i++) {
                manySlotIds.add(i);
            }
            testDate = LocalDate.now().plusDays(7);
        }

        private void injectDAOs(ProgrammazioneService service,
                                FilmDAO filmDAO,
                                SalaDAO salaDAO,
                                SlotDAO slotDAO,
                                ProiezioneDAO proiezioneDAO) {
            try {
                java.lang.reflect.Field filmDAOField =
                        ProgrammazioneService.class.getDeclaredField("filmDAO");
                filmDAOField.setAccessible(true);
                filmDAOField.set(service, filmDAO);

                java.lang.reflect.Field salaDAOField =
                        ProgrammazioneService.class.getDeclaredField("salaDAO");
                salaDAOField.setAccessible(true);
                salaDAOField.set(service, salaDAO);

                java.lang.reflect.Field slotDAOField =
                        ProgrammazioneService.class.getDeclaredField("slotDAO");
                slotDAOField.setAccessible(true);
                slotDAOField.set(service, slotDAO);

                java.lang.reflect.Field proiezioneDAOField =
                        ProgrammazioneService.class.getDeclaredField("proiezioneDAO");
                proiezioneDAOField.setAccessible(true);
                proiezioneDAOField.set(service, proiezioneDAO);
            } catch (NoSuchFieldException | IllegalAccessException e) {
                throw new RuntimeException("Errore durante l'iniezione dei DAO", e);
            }
        }
    }

    @Benchmark
    public void aggiungiProiezioneFewSlots(ProgrammazioneState state, Blackhole bh) {
        boolean result = state.programmazioneService.aggiungiProiezione(
                state.testFilm.getId(),
                state.testSala.getId(),
                state.fewSlotIds,
                state.testDate
        );
        bh.consume(result);
    }

    @Benchmark
    public void aggiungiProiezioneManySlots(ProgrammazioneState state, Blackhole bh) {
        boolean result = state.programmazioneService.aggiungiProiezione(
                state.testFilm.getId(),
                state.testSala.getId(),
                state.manySlotIds,
                state.testDate
        );
        bh.consume(result);
    }

    @Benchmark
    public void aggiungiProiezioneFilmNonEsistente(ProgrammazioneState state, Blackhole bh) {
        boolean result = state.programmazioneService.aggiungiProiezione(
                999,
                state.testSala.getId(),
                state.fewSlotIds,
                state.testDate
        );
        bh.consume(result);
    }

    @Benchmark
    public void aggiungiProiezioneSalaNonEsistente(ProgrammazioneState state, Blackhole bh) {
        boolean result = state.programmazioneService.aggiungiProiezione(
                state.testFilm.getId(),
                999,
                state.fewSlotIds,
                state.testDate
        );
        bh.consume(result);
    }
}
