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
public class ProgrammazioneServiceBenchmark {

    @State(Scope.Benchmark)
    public static class SlotState {
        public List<Integer> hours;

        @Setup
        public void setup() {
            hours = new ArrayList<>();
            for (int i = 0; i < 240; i++) {
                hours.add(i);
            }
        }
    }

    @Benchmark
    public void filterPrimeTimeSlots(SlotState state, Blackhole bh) {
        List<Integer> result = state.hours.stream()
            .filter(h -> h >= 18 && h <= 23)
            .toList();
        bh.consume(result);
    }

    @Benchmark
    public void countAfternoonSlots(SlotState state, Blackhole bh) {
        long count = state.hours.stream()
            .filter(h -> h >= 12 && h < 18)
            .count();
        bh.consume(count);
    }
}
