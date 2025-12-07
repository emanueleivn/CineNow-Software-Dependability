package it.unisa.application.benchmark.services;

import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Warmup(iterations = 2, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 3, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(1)
public class PrenotazioneServiceBenchmark {

    @State(Scope.Benchmark)
    public static class PrenotazioneState {
        public List<Integer> seatNumbers;

        @Setup
        public void setup() {
            seatNumbers = new ArrayList<>();
            for (int i = 1; i <= 500; i++) {
                seatNumbers.add(i);
            }
        }
    }

    @Benchmark
    public void countFreeSeats(PrenotazioneState state, Blackhole bh) {
        long count = state.seatNumbers.stream()
            .filter(s -> s % 2 == 0)
            .count();
        bh.consume(count);
    }

    @Benchmark
    public void findFirstAvailable(PrenotazioneState state, Blackhole bh) {
        Integer first = state.seatNumbers.stream()
            .filter(s -> s > 250)
            .findFirst()
            .orElse(null);
        bh.consume(first);
    }
}
