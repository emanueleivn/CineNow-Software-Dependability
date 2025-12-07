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
public class CatalogoServiceBenchmark {

    @State(Scope.Benchmark)
    public static class CatalogoState {
        public List<String> filmTitles;

        @Setup
        public void setup() {
            filmTitles = new ArrayList<>();
            for (int i = 0; i < 1000; i++) {
                filmTitles.add("Film " + i);
            }
        }
    }

    @Benchmark
    public void searchFilmTitles(CatalogoState state, Blackhole bh) {
        List<String> result = state.filmTitles.stream()
            .filter(f -> f.contains("Film"))
            .toList();
        bh.consume(result);
    }

    @Benchmark
    public void countFilms(CatalogoState state, Blackhole bh) {
        long count = state.filmTitles.stream()
            .filter(f -> f.startsWith("Film"))
            .count();
        bh.consume(count);
    }
}
