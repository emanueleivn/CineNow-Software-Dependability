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
public class ProgrammazioneSedeServiceBenchmark {

    @State(Scope.Benchmark)
    public static class ProiezioniState {
        public List<LocalDate> dates;

        @Setup
        public void setup() {
            dates = new ArrayList<>();
            for (int i = 0; i < 500; i++) {
                dates.add(LocalDate.now().plusDays(i));
            }
        }
    }

    @Benchmark
    public void filterUpcomingDates(ProiezioniState state, Blackhole bh) {
        List<LocalDate> result = state.dates.stream()
            .filter(d -> d.isAfter(LocalDate.now()))
            .toList();
        bh.consume(result);
    }

    @Benchmark
    public void countUpcoming(ProiezioniState state, Blackhole bh) {
        long count = state.dates.stream()
            .filter(d -> d.isAfter(LocalDate.now()))
            .count();
        bh.consume(count);
    }
}
