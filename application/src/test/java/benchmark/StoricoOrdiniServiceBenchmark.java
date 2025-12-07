package benchmark;

import it.unisa.application.model.dao.PrenotazioneDAO;
import it.unisa.application.model.entity.*;
import it.unisa.application.sottosistemi.gestione_prenotazione.service.StoricoOrdiniService;
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
 * Benchmark per StoricoOrdiniService.storicoOrdini().
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 15, time = 1)
@Measurement(iterations = 20, time = 1)
@State(Scope.Benchmark)
public class StoricoOrdiniServiceBenchmark {

    private StoricoOrdiniService storicoOrdiniService;
    private Cliente testCliente;
    private Cliente clienteWithNoOrders;

    @Setup
    public void setup() {
        testCliente = new Cliente("test@example.com", "hashedpassword", "Mario", "Rossi");
        clienteWithNoOrders = new Cliente("empty@example.com", "hashedpassword", "Giovanni", "Bianchi");

        Sede sede = new Sede(1, "Sede Test", "Via Test");
        Sala sala = new Sala(1, 1, 100, sede);
        Slot slot = new Slot(1, Time.valueOf(LocalTime.of(20, 0)));
        Film film = new Film(1, "Film Test", "Drammatico", "PG-13", 120, new byte[0], "Test", true);
        Proiezione proiezione = new Proiezione(1, sala, film, LocalDate.now().plusDays(1), slot);

        List<Prenotazione> manyOrders = new ArrayList<>();
        for (int i = 1; i <= 50; i++) {
            Prenotazione p = new Prenotazione(i, testCliente, proiezione);
            manyOrders.add(p);
        }

        PrenotazioneDAO prenotazioneDAOMock = mock(PrenotazioneDAO.class);
        when(prenotazioneDAOMock.retrieveAllByCliente(testCliente))
                .thenReturn(manyOrders);
        when(prenotazioneDAOMock.retrieveAllByCliente(clienteWithNoOrders))
                .thenReturn(new ArrayList<>());

        storicoOrdiniService = mock(StoricoOrdiniService.class, CALLS_REAL_METHODS);
        injectDAO(storicoOrdiniService, prenotazioneDAOMock);
    }

    private void injectDAO(StoricoOrdiniService service, PrenotazioneDAO prenotazioneDAO) {
        try {
            java.lang.reflect.Field field =
                    StoricoOrdiniService.class.getDeclaredField("prenotazioneDAO");
            field.setAccessible(true);
            field.set(service, prenotazioneDAO);
        } catch (NoSuchFieldException | IllegalAccessException e) {
            throw new RuntimeException("Errore durante l'iniezione del DAO", e);
        }
    }

    @Benchmark
    public void storicoOrdiniWithManyOrders(Blackhole bh) {
        List<Prenotazione> result = storicoOrdiniService.storicoOrdini(testCliente);
        bh.consume(result);
    }

    @Benchmark
    public void storicoOrdiniWithNoOrders(Blackhole bh) {
        List<Prenotazione> result = storicoOrdiniService.storicoOrdini(clienteWithNoOrders);
        bh.consume(result);
    }

    @Benchmark
    public void storicoOrdiniWithNullCliente(Blackhole bh) {
        try {
            List<Prenotazione> result = storicoOrdiniService.storicoOrdini(null);
            bh.consume(result);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        }
    }
}
