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
public class RegistrazioneServiceBenchmark {

    @State(Scope.Benchmark)
    public static class UtenteState {
        public List<String> emails;

        @Setup
        public void setup() {
            emails = new ArrayList<>();
            for (int i = 0; i < 500; i++) {
                emails.add("user" + i + "@test.com");
            }
        }
    }

    @Benchmark
    public void validateEmails(UtenteState state, Blackhole bh) {
        List<String> result = state.emails.stream()
            .filter(e -> e.contains("@") && e.contains("."))
            .toList();
        bh.consume(result);
    }

    @Benchmark
    public void filterValidDomains(UtenteState state, Blackhole bh) {
        List<String> result = state.emails.stream()
            .filter(e -> e.endsWith(".com"))
            .toList();
        bh.consume(result);
    }
}
