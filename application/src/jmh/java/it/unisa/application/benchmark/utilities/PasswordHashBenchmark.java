package it.unisa.application.benchmark.utilities;

import it.unisa.application.utilities.PasswordHash;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.util.concurrent.TimeUnit;

/**
 * Benchmark per PasswordHash - SHA-512 hashing
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Warmup(iterations = 2)
@Measurement(iterations = 3)
@Fork(1)
@State(Scope.Benchmark)
public class PasswordHashBenchmark {

    private String shortPassword;
    private String mediumPassword;
    private String longPassword;

    @Setup
    public void setup() {
        shortPassword = "pass1234";
        mediumPassword = "MySecurePassword12345";
        longPassword = "MyVerySecurePasswordWith64CharactersLongEnoughForAnySecurityRequirement";
    }

    @Benchmark
    public void hashShortPassword(Blackhole bh) {
        String result = PasswordHash.hash(shortPassword);
        bh.consume(result);
    }

    @Benchmark
    public void hashMediumPassword(Blackhole bh) {
        String result = PasswordHash.hash(mediumPassword);
        bh.consume(result);
    }

    @Benchmark
    public void hashLongPassword(Blackhole bh) {
        String result = PasswordHash.hash(longPassword);
        bh.consume(result);
    }
}
