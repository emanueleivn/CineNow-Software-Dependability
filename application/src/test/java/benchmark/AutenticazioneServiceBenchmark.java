package benchmark;

import it.unisa.application.model.dao.ClienteDAO;
import it.unisa.application.model.dao.UtenteDAO;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.model.entity.Utente;
import it.unisa.application.sottosistemi.gestione_utente.service.AutenticazioneService;
import it.unisa.application.utilities.PasswordHash;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.util.concurrent.TimeUnit;

import static org.mockito.Mockito.*;

/**
 * Benchmark per AutenticazioneService.login()
 * Testa login valido, password sbagliata e utente inesistente
 * con hashing reale della password.
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 15, time = 1)
@Measurement(iterations = 20, time = 1)
@State(Scope.Benchmark)
public class AutenticazioneServiceBenchmark {

    private AutenticazioneService autenticazioneService;
    private String validEmail;
    private String validPassword;
    private String invalidPassword;
    private String nonExistentEmail;
    private String validPasswordHash;

    @Setup
    public void setup() {
        validEmail = "test@example.com";
        validPassword = "SecurePassword123";
        invalidPassword = "WrongPassword";
        nonExistentEmail = "nonexistent@example.com";
        validPasswordHash = PasswordHash.hash(validPassword);

        // DAO mock
        UtenteDAO utenteDAOMock = mock(UtenteDAO.class);
        ClienteDAO clienteDAOMock = mock(ClienteDAO.class);

        // Comportamento dei mock
        when(utenteDAOMock.retrieveByEmail(validEmail))
                .thenReturn(new Utente(validEmail, validPasswordHash, "cliente"));
        when(utenteDAOMock.retrieveByEmail(nonExistentEmail))
                .thenReturn(null);

        when(clienteDAOMock.retrieveByEmail(eq(validEmail), eq(validPasswordHash)))
                .thenReturn(new Cliente(validEmail, validPasswordHash, "Mario", "Rossi"));

        // Service reale, ma con DAO iniettati via reflection
        autenticazioneService = mock(AutenticazioneService.class, CALLS_REAL_METHODS);
        injectDAOs(autenticazioneService, utenteDAOMock, clienteDAOMock);
    }

    private void injectDAOs(AutenticazioneService service,
                            UtenteDAO utenteDAO,
                            ClienteDAO clienteDAO) {
        try {
            java.lang.reflect.Field utenteDAOField =
                    AutenticazioneService.class.getDeclaredField("utenteDAO");
            utenteDAOField.setAccessible(true);
            utenteDAOField.set(service, utenteDAO);

            java.lang.reflect.Field clienteDAOField =
                    AutenticazioneService.class.getDeclaredField("clienteDAO");
            clienteDAOField.setAccessible(true);
            clienteDAOField.set(service, clienteDAO);
        } catch (NoSuchFieldException | IllegalAccessException e) {
            throw new RuntimeException("Errore durante l'iniezione dei DAO", e);
        }
    }

    @Benchmark
    public void loginValidCredentials(Blackhole bh) {
        Utente result = autenticazioneService.login(validEmail, validPassword);
        bh.consume(result);
    }

    @Benchmark
    public void loginInvalidPassword(Blackhole bh) {
        Utente result = autenticazioneService.login(validEmail, invalidPassword);
        bh.consume(result);
    }

    @Benchmark
    public void loginNonExistentUser(Blackhole bh) {
        Utente result = autenticazioneService.login(nonExistentEmail, validPassword);
        bh.consume(result);
    }
}
