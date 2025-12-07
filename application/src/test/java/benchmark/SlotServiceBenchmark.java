package benchmark;

import it.unisa.application.model.dao.FilmDAO;
import it.unisa.application.model.dao.ProiezioneDAO;
import it.unisa.application.model.dao.SlotDAO;
import it.unisa.application.model.entity.Film;
import it.unisa.application.model.entity.Slot;
import it.unisa.application.sottosistemi.gestione_sala.service.SlotService;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.sql.Time;
import java.time.LocalDate;
import java.time.LocalTime;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;

import static org.mockito.Mockito.*;

/**
 * Benchmark per SlotService.slotDisponibili().
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 15, time = 1)
@Measurement(iterations = 20, time = 1)
public class SlotServiceBenchmark {

    @State(Scope.Benchmark)
    public static class SlotServiceState {
        public SlotService slotService;
        public int filmId;
        public int salaId;
        public LocalDate startDate;
        public LocalDate endDate;

        @Setup
        public void setup() {
            SlotDAO slotDAOMock = mock(SlotDAO.class);
            ProiezioneDAO proiezioneDAOMock = mock(ProiezioneDAO.class);
            FilmDAO filmDAOMock = mock(FilmDAO.class);

            List<Slot> slots = new ArrayList<>();
            for (int i = 1; i <= 8; i++) {
                LocalTime startTime = LocalTime.of(9 + (i - 1) / 2,
                        (i - 1) % 2 == 0 ? 0 : 30);
                slots.add(new Slot(i, Time.valueOf(startTime)));
            }
            when(slotDAOMock.retrieveAllSlots()).thenReturn(slots);
            when(proiezioneDAOMock
                    .retrieveProiezioneBySalaSlotAndData(anyInt(), anyInt(), any(LocalDate.class)))
                    .thenReturn(null);
            when(filmDAOMock.retrieveById(anyInt()))
                    .thenReturn(new Film(1, "Film Test", "Drammatico",
                            "PG-13", 120, new byte[0], "Test", true));

            slotService = mock(SlotService.class, CALLS_REAL_METHODS);
            injectDAOs(slotService, slotDAOMock, proiezioneDAOMock, filmDAOMock);

            filmId = 1;
            salaId = 1;
            startDate = LocalDate.now().plusDays(1);
            endDate = LocalDate.now().plusDays(14);
        }

        private void injectDAOs(SlotService service,
                                SlotDAO slotDAO,
                                ProiezioneDAO proiezioneDAO,
                                FilmDAO filmDAO) {
            try {
                java.lang.reflect.Field slotDAOField =
                        SlotService.class.getDeclaredField("slotDAO");
                slotDAOField.setAccessible(true);
                slotDAOField.set(service, slotDAO);

                java.lang.reflect.Field proiezioneDAOField =
                        SlotService.class.getDeclaredField("proiezioneDAO");
                proiezioneDAOField.setAccessible(true);
                proiezioneDAOField.set(service, proiezioneDAO);

                java.lang.reflect.Field filmDAOField =
                        SlotService.class.getDeclaredField("filmDAO");
                filmDAOField.setAccessible(true);
                filmDAOField.set(service, filmDAO);
            } catch (NoSuchFieldException | IllegalAccessException e) {
                throw new RuntimeException("Errore durante l'iniezione dei DAO", e);
            }
        }
    }

    @Benchmark
    public void slotDisponibiliShortRange(SlotServiceState state, Blackhole bh) {
        try {
            Map<String, Object> result = state.slotService.slotDisponibili(
                    state.filmId,
                    state.salaId,
                    state.startDate,
                    state.startDate.plusDays(1)
            );
            bh.consume(result);
        } catch (Exception e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void slotDisponibiliLongRange(SlotServiceState state, Blackhole bh) {
        try {
            Map<String, Object> result = state.slotService.slotDisponibili(
                    state.filmId,
                    state.salaId,
                    state.startDate,
                    state.endDate
            );
            bh.consume(result);
        } catch (Exception e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void slotDisponibiliSingleDay(SlotServiceState state, Blackhole bh) {
        try {
            Map<String, Object> result = state.slotService.slotDisponibili(
                    state.filmId,
                    state.salaId,
                    state.startDate,
                    state.startDate
            );
            bh.consume(result);
        } catch (Exception e) {
            bh.consume(e);
        }
    }
}
