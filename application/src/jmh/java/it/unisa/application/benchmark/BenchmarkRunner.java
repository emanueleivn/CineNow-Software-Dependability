package it.unisa.application.benchmark;

import org.openjdk.jmh.Main;

/**
 * Entry point per eseguire tutti i benchmark JMH del progetto CineNow
 */
public class BenchmarkRunner {
    public static void main(String[] args) throws Exception {
        // Esegui i benchmark JMH con timeout ridotto per evitare blocchi
        String[] jmhArgs = {
            ".*ServiceBenchmark.*",  // Esegui tutti i benchmark dei servizi
            "-i", "3",                // 3 iterazioni di misurazione
            "-w", "2",                // 2 iterazioni di warmup
            "-f", "1",                // 1 fork
            "-t", "1",                // 1 thread
            "-bm", "avgt",            // Average time mode
            "-tu", "us",              // Time unit: microsecondi
            "-to", "10s"              // Timeout: 10 secondi per iterazione
        };

        Main.main(jmhArgs);
    }
}
