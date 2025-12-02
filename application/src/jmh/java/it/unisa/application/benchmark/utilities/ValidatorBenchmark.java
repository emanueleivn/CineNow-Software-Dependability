package it.unisa.application.benchmark.utilities;

import it.unisa.application.utilities.EmailValidator;
import it.unisa.application.utilities.CampoValidator;
import it.unisa.application.utilities.ValidateStrategyManager;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.TimeUnit;

/**
 * Benchmark per i validatori - email, campo, strategy manager
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Warmup(iterations = 2)
@Measurement(iterations = 3)
@Fork(1)
@State(Scope.Benchmark)
public class ValidatorBenchmark {

    private EmailValidator emailValidator;
    private CampoValidator campoValidator;
    private ValidateStrategyManager strategyManager;

    private String validEmail;
    private String invalidEmailNoAt;
    private String validName;
    private String invalidNameWithNumbers;

    private Map<String, String> validBatchInputs;
    private Map<String, String> invalidBatchInputs;

    @Setup
    public void setup() {
        emailValidator = new EmailValidator();
        campoValidator = new CampoValidator();
        strategyManager = new ValidateStrategyManager();

        validEmail = "user@example.com";
        invalidEmailNoAt = "user.example.com";
        validName = "Mario";
        invalidNameWithNumbers = "Mario123";

        validBatchInputs = new HashMap<>();
        validBatchInputs.put("email", "test@example.com");
        validBatchInputs.put("campo", "Giovanni");

        invalidBatchInputs = new HashMap<>();
        invalidBatchInputs.put("email", "invalid.email");
        invalidBatchInputs.put("campo", "Mario<alert>");
    }

    @Benchmark
    public void validateValidEmail(Blackhole bh) {
        boolean result = emailValidator.validate(validEmail);
        bh.consume(result);
    }

    @Benchmark
    public void validateInvalidEmailNoAt(Blackhole bh) {
        boolean result = emailValidator.validate(invalidEmailNoAt);
        bh.consume(result);
    }

    @Benchmark
    public void validateValidName(Blackhole bh) {
        boolean result = campoValidator.validate(validName);
        bh.consume(result);
    }

    @Benchmark
    public void validateInvalidNameWithNumbers(Blackhole bh) {
        boolean result = campoValidator.validate(invalidNameWithNumbers);
        bh.consume(result);
    }

    @Benchmark
    public void validateBatchValid(Blackhole bh) {
        boolean result = strategyManager.validate(validBatchInputs);
        bh.consume(result);
    }

    @Benchmark
    public void validateBatchInvalid(Blackhole bh) {
        boolean result = strategyManager.validate(invalidBatchInputs);
        bh.consume(result);
    }
}
