package benchmark;

import it.unisa.application.model.dao.ProiezioneDAO;
import it.unisa.application.model.entity.*;
import it.unisa.application.sottosistemi.gestione_sede.service.ProgrammazioneSedeService;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.sql.Time;
import java.time.LocalDate;
import java.time.LocalTime;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.mockito.Mockito.*;

/**
 * Benchmark per ProgrammazioneSedeService.
 * Testa getProgrammazione(sedeId) e getProiezioniFilm(filmId, sedeId).
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 15, time = 1)
@Measurement(iterations = 20, time = 1)
public class ProgrammazioneSedeServiceBenchmark {

    @State(Scope.Benchmark)
    public static class ProgrammazioneSedeState {
        public ProgrammazioneSedeService programmazioneSedeService;
        public int sedeId;
        public int filmId;
        public List<Proiezione> manyProiezioni;

        @Setup
        public void setup() {
            sedeId = 1;
            filmId = 1;

            Sede sede = new Sede(sedeId, "Sede Test", "Via Test");
            Sala sala = new Sala(1, 1, 100, sede);
            Slot slot = new Slot(1, Time.valueOf(LocalTime.of(20, 0)));
            Film film = new Film(filmId, "Film Test", "Drammatico", "PG-13",
                    120, new byte[0], "Test", true);

            manyProiezioni = new ArrayList<>();
            for (int i = 0; i < 100; i++) {
                Proiezione p = new Proiezione(
                        i,
                        sala,
                        film,
                        LocalDate.now().plusDays(i % 30),
                        slot
                );
                manyProiezioni.add(p);
            }

            ProiezioneDAO proiezioneDAOMock = mock(ProiezioneDAO.class);

            when(proiezioneDAOMock.retrieveAllBySede(sedeId))
                    .thenReturn(manyProiezioni);
            when(proiezioneDAOMock.retrieveAllBySede(999))
                    .thenReturn(new ArrayList<>());

            List<Proiezione> weeklyProiezioni = manyProiezioni.stream()
                    .filter(p -> !p.getDataProiezione().isBefore(LocalDate.now())
                            && !p.getDataProiezione().isAfter(LocalDate.now().plusDays(7)))
                    .toList();

            when(proiezioneDAOMock.retrieveByFilm(any(Film.class), any(Sede.class)))
                    .thenReturn(weeklyProiezioni);

            programmazioneSedeService =
                    mock(ProgrammazioneSedeService.class, CALLS_REAL_METHODS);
            injectProiezioneDAO(programmazioneSedeService, proiezioneDAOMock);
        }

        private void injectProiezioneDAO(ProgrammazioneSedeService service,
                                         ProiezioneDAO dao) {
            try {
                java.lang.reflect.Field field =
                        ProgrammazioneSedeService.class.getDeclaredField("proiezioneDAO");
                field.setAccessible(true);
                field.set(service, dao);
            } catch (NoSuchFieldException | IllegalAccessException e) {
                throw new RuntimeException("Errore durante l'iniezione di ProiezioneDAO", e);
            }
        }
    }

    @Benchmark
    public void getProgrammazioneFewShows(ProgrammazioneSedeState state, Blackhole bh) {
        List<Proiezione> result = state.programmazioneSedeService.getProgrammazione(state.sedeId);
        bh.consume(result);
    }

    @Benchmark
    public void getProiezioniFilmWeekly(ProgrammazioneSedeState state, Blackhole bh) {
        List<Proiezione> result = state.programmazioneSedeService
                .getProiezioniFilm(state.filmId, state.sedeId);
        bh.consume(result);
    }

    @Benchmark
    public void getProiezioniFilmNoResults(ProgrammazioneSedeState state, Blackhole bh) {
        List<Proiezione> result = state.programmazioneSedeService
                .getProiezioniFilm(999, state.sedeId);
        bh.consume(result);
    }
}
