package benchmark;

import it.unisa.application.model.dao.PostoProiezioneDAO;
import it.unisa.application.model.dao.PrenotazioneDAO;
import it.unisa.application.model.entity.*;
import it.unisa.application.sottosistemi.gestione_prenotazione.service.PrenotazioneService;
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
 * Benchmark per PrenotazioneService.aggiungiOrdine()
 * Testa la creazione di prenotazioni con logica reale.
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 15, time = 1)
@Measurement(iterations = 40, time = 1)
@State(Scope.Benchmark)
public class PrenotazioneServiceBenchmark {

    @State(Scope.Benchmark)
    public static class PrenotazioneState {
        public PrenotazioneService prenotazioneService;
        public Cliente testCliente;
        public Proiezione testProiezione;
        public List<PostoProiezione> fewAvailableSeats;
        public List<PostoProiezione> manyAvailableSeats;
        public List<PostoProiezione> occupiedSeats;

        @Setup
        public void setup() {
            PrenotazioneDAO prenotazioneDAOMock = mock(PrenotazioneDAO.class);
            PostoProiezioneDAO postoProiezioneDAOMock = mock(PostoProiezioneDAO.class);

            when(prenotazioneDAOMock.create(any(Prenotazione.class))).thenReturn(true);
            when(postoProiezioneDAOMock.occupaPosto(any(PostoProiezione.class), anyInt()))
                    .thenReturn(true);

            prenotazioneService = mock(PrenotazioneService.class, CALLS_REAL_METHODS);
            injectDAOs(prenotazioneService, prenotazioneDAOMock, postoProiezioneDAOMock);

            testCliente = new Cliente("test@example.com", "hashedpassword", "Mario", "Rossi");

            Sede sede = new Sede(1, "Sede Test", "Via Test");
            Sala sala = new Sala(1, 1, 100, sede);
            Slot slot = new Slot(1, Time.valueOf(LocalTime.of(20, 0)));
            Film film = new Film(1, "Film Test", "Drammatico", "PG-13", 120, new byte[0], "Test", true);
            testProiezione = new Proiezione(1, sala, film, LocalDate.now().plusDays(1), slot);

            fewAvailableSeats = new ArrayList<>();
            for (int i = 1; i <= 2; i++) {
                Posto posto = new Posto(sala, 'A', i);
                PostoProiezione pp = new PostoProiezione(posto, testProiezione);
                pp.setStato(true);
                fewAvailableSeats.add(pp);
            }

            manyAvailableSeats = new ArrayList<>();
            for (int row = 0; row < 5; row++) {
                for (int col = 1; col <= 2; col++) {
                    Posto posto = new Posto(sala, (char) ('A' + row), col);
                    PostoProiezione pp = new PostoProiezione(posto, testProiezione);
                    pp.setStato(true);
                    manyAvailableSeats.add(pp);
                }
            }

            occupiedSeats = new ArrayList<>();
            for (int i = 1; i <= 2; i++) {
                Posto posto = new Posto(sala, 'B', i);
                PostoProiezione pp = new PostoProiezione(posto, testProiezione);
                pp.setStato(false);
                occupiedSeats.add(pp);
            }
        }

        private void injectDAOs(PrenotazioneService service,
                                PrenotazioneDAO prenotazioneDAO,
                                PostoProiezioneDAO postoProiezioneDAO) {
            try {
                java.lang.reflect.Field prenotazioneDAOField =
                        PrenotazioneService.class.getDeclaredField("prenotazioneDAO");
                prenotazioneDAOField.setAccessible(true);
                prenotazioneDAOField.set(service, prenotazioneDAO);

                java.lang.reflect.Field postoProiezioneDAOField =
                        PrenotazioneService.class.getDeclaredField("postoProiezioneDAO");
                postoProiezioneDAOField.setAccessible(true);
                postoProiezioneDAOField.set(service, postoProiezioneDAO);
            } catch (NoSuchFieldException | IllegalAccessException e) {
                throw new RuntimeException("Errore durante l'iniezione dei DAO", e);
            }
        }
    }

    @Benchmark
    public void aggiungiOrdineWithFewSeats(PrenotazioneState state, Blackhole bh) {
        try {
            state.prenotazioneService.aggiungiOrdine(
                    state.testCliente,
                    state.fewAvailableSeats,
                    state.testProiezione
            );
            bh.consume(true);
        } catch (Exception e) {
            bh.consume(false);
        }
    }

    @Benchmark
    public void aggiungiOrdineWithManySeats(PrenotazioneState state, Blackhole bh) {
        try {
            state.prenotazioneService.aggiungiOrdine(
                    state.testCliente,
                    state.manyAvailableSeats,
                    state.testProiezione
            );
            bh.consume(true);
        } catch (Exception e) {
            bh.consume(false);
        }
    }

    @Benchmark
    public void aggiungiOrdineWithOccupiedSeats(PrenotazioneState state, Blackhole bh) {
        try {
            state.prenotazioneService.aggiungiOrdine(
                    state.testCliente,
                    state.occupiedSeats,
                    state.testProiezione
            );
            bh.consume(true);
        } catch (Exception e) {
            bh.consume(false);
        }
    }

    @Benchmark
    public void aggiungiOrdineWithNullCliente(PrenotazioneState state, Blackhole bh) {
        try {
            state.prenotazioneService.aggiungiOrdine(
                    null,
                    state.fewAvailableSeats,
                    state.testProiezione
            );
            bh.consume(true);
        } catch (Exception e) {
            bh.consume(false);
        }
    }
}
