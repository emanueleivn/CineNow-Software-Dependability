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
public class AutenticazioneServiceBenchmark {

    @State(Scope.Benchmark)
    public static class LoginState {
        public List<String> userEmails;

        @Setup
        public void setup() {
            userEmails = new ArrayList<>();
            for (int i = 0; i < 500; i++) {
                userEmails.add("admin" + i + "@test.com");
            }
        }
    }

    @Benchmark
    public void findUserByEmail(LoginState state, Blackhole bh) {
        String found = state.userEmails.stream()
            .filter(e -> e.equals("admin250@test.com"))
            .findFirst()
            .orElse(null);
        bh.consume(found);
    }

    @Benchmark
    public void filterAdminUsers(LoginState state, Blackhole bh) {
        List<String> result = state.userEmails.stream()
            .filter(e -> e.startsWith("admin"))
            .toList();
        bh.consume(result);
    }
}
