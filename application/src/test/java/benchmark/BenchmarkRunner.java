package benchmark;

import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

/**
 * Runner principale per eseguire i benchmark JMH.
 * Modifica la classe nel metodo include() per eseguire benchmark diversi.
 *
 * Per eseguire: mvn clean compile test-compile exec:java
 */
public class BenchmarkRunner {
    public static void main(String[] args) throws Exception {
        Options opt = new OptionsBuilder()
                .include(AutenticazioneServiceBenchmark.class.getSimpleName())
                // .include(CatalogoServiceBenchmark.class.getSimpleName())
                .include(PasswordHashBenchmark.class.getSimpleName())
                // .include(PrenotazioneServiceBenchmark.class.getSimpleName())
                // .include(ProgrammazioneSedeServiceBenchmark.class.getSimpleName())
                // .include(ProgrammazioneServiceBenchmark.class.getSimpleName())
                // .include(RegistrazioneServiceBenchmark.class.getSimpleName())
                // .include(SlotServiceBenchmark.class.getSimpleName())
                // .include(StoricoOrdiniServiceBenchmark.class.getSimpleName())
                // .include(ValidatorBenchmark.class.getSimpleName())
                .forks(1)
                .build();

        new Runner(opt).run();
    }
}
