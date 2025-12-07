package it.unisa.application.benchmark.services;

import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Warmup(iterations = 2, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 3, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(1)
public class StoricoOrdiniServiceBenchmark {

    @State(Scope.Benchmark)
    public static class StoricoState {
        public List<LocalDate> prenotazioniDate;

        @Setup
        public void setup() {
            prenotazioniDate = new ArrayList<>();
            for (int i = 0; i < 500; i++) {
                prenotazioniDate.add(LocalDate.now().minusDays(i));
            }
        }
    }

    @Benchmark
    public void filterRecentBookings(StoricoState state, Blackhole bh) {
        List<LocalDate> result = state.prenotazioniDate.stream()
            .filter(d -> d.isAfter(LocalDate.now().minusDays(30)))
            .toList();
        bh.consume(result);
    }

    @Benchmark
    public void countOldBookings(StoricoState state, Blackhole bh) {
        long count = state.prenotazioniDate.stream()
            .filter(d -> d.isBefore(LocalDate.now().minusDays(60)))
            .count();
        bh.consume(count);
    }
}
