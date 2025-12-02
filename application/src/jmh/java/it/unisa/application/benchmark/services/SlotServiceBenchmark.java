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
public class SlotServiceBenchmark {

    @State(Scope.Benchmark)
    public static class SlotsData {
        public List<Integer> slotIds;

        @Setup
        public void setup() {
            slotIds = new ArrayList<>();
            for (int i = 1; i <= 500; i++) {
                slotIds.add(i);
            }
        }
    }

    @Benchmark
    public void getAvailableSlots(SlotsData state, Blackhole bh) {
        List<Integer> result = state.slotIds.stream()
            .filter(s -> s <= 200)
            .toList();
        bh.consume(result);
    }

    @Benchmark
    public void findSlotById(SlotsData state, Blackhole bh) {
        Integer found = state.slotIds.stream()
            .filter(s -> s == 250)
            .findFirst()
            .orElse(null);
        bh.consume(found);
    }
}
