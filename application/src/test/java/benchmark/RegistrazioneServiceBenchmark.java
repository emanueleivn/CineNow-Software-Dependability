package benchmark;

import it.unisa.application.model.dao.ClienteDAO;
import it.unisa.application.model.dao.UtenteDAO;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.sottosistemi.gestione_utente.service.RegistrazioneService;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.util.concurrent.TimeUnit;

import static org.mockito.Mockito.*;

/**
 * Benchmark per RegistrazioneService.registrazione().
 * Testa registrazione valida e casi di input errato.
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 15, time = 1)
@Measurement(iterations = 20, time = 1)
@State(Scope.Benchmark)
public class RegistrazioneServiceBenchmark {

    private RegistrazioneService registrazioneService;
    private String newEmail;
    private String validPassword;
    private String validNome;
    private String validCognome;
    private String shortPassword;
    private String invalidEmail;

    @Setup
    public void setup() {
        newEmail = "newuser@example.com";
        validPassword = "SecurePassword123";
        validNome = "Giovanni";
        validCognome = "Bianchi";
        shortPassword = "pass";
        invalidEmail = "notanemail";

        UtenteDAO utenteDAOMock = mock(UtenteDAO.class);
        ClienteDAO clienteDAOMock = mock(ClienteDAO.class);

        when(utenteDAOMock.retrieveByEmail(newEmail)).thenReturn(null);
        when(utenteDAOMock.retrieveByEmail(invalidEmail)).thenReturn(null);
        when(clienteDAOMock.create(any(Cliente.class))).thenReturn(true);

        registrazioneService = mock(RegistrazioneService.class, CALLS_REAL_METHODS);
        injectDAOs(registrazioneService, utenteDAOMock, clienteDAOMock);
    }

    private void injectDAOs(RegistrazioneService service,
                            UtenteDAO utenteDAO,
                            ClienteDAO clienteDAO) {
        try {
            java.lang.reflect.Field utenteDAOField =
                    RegistrazioneService.class.getDeclaredField("utenteDAO");
            utenteDAOField.setAccessible(true);
            utenteDAOField.set(service, utenteDAO);

            java.lang.reflect.Field clienteDAOField =
                    RegistrazioneService.class.getDeclaredField("clienteDAO");
            clienteDAOField.setAccessible(true);
            clienteDAOField.set(service, clienteDAO);
        } catch (NoSuchFieldException | IllegalAccessException e) {
            throw new RuntimeException("Errore durante l'iniezione dei DAO", e);
        }
    }

    @Benchmark
    public void registrazioneValida(Blackhole bh) {
        Cliente result = registrazioneService.registrazione(
                newEmail, validPassword, validNome, validCognome);
        bh.consume(result);
    }

    @Benchmark
    public void registrazionePasswordCorta(Blackhole bh) {
        Cliente result = registrazioneService.registrazione(
                newEmail, shortPassword, validNome, validCognome);
        bh.consume(result);
    }

    @Benchmark
    public void registrazioneEmailInvalida(Blackhole bh) {
        Cliente result = registrazioneService.registrazione(
                invalidEmail, validPassword, validNome, validCognome);
        bh.consume(result);
    }
}
