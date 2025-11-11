package unit.test_gestione_utente;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.ClienteDAO;
import it.unisa.application.model.dao.UtenteDAO;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.sottosistemi.gestione_utente.service.RegistrazioneService;
import it.unisa.application.utilities.PasswordHash;
import it.unisa.application.utilities.ValidateStrategyManager;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.*;
import org.mockito.junit.jupiter.MockitoExtension;

import javax.sql.DataSource;
import java.lang.reflect.Field;
import java.sql.Connection;
import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test di unità per RegistrazioneService.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class RegistrazioneServiceTest {

    @Mock private UtenteDAO utenteDAO;
    @Mock private ClienteDAO clienteDAO;
    @Mock private ValidateStrategyManager validationManager;

    @Mock private DataSource mockDataSource;
    @Mock private Connection mockConnection;

    private MockedStatic<DataSourceSingleton> mockedDataSourceSingleton;
    private MockedStatic<PasswordHash> mockedPasswordHash;

    private RegistrazioneService service;

    @BeforeEach
    void setUp() throws Exception {
        // Mock statico DataSourceSingleton
        mockedDataSourceSingleton = mockStatic(DataSourceSingleton.class);
        mockedDataSourceSingleton.when(DataSourceSingleton::getInstance).thenReturn(mockDataSource);
        lenient().when(mockDataSource.getConnection()).thenReturn(mockConnection);

        // Mock statico PasswordHash
        mockedPasswordHash = mockStatic(PasswordHash.class);

        // Istanzia la classe da testare e sostituisci i DAO e il validator manager
        service = new RegistrazioneService();
        injectMock("utenteDAO", utenteDAO);
        injectMock("clienteDAO", clienteDAO);
        injectMock("validationManager", validationManager);
    }

    private void injectMock(String fieldName, Object mock) throws Exception {
        Field field = RegistrazioneService.class.getDeclaredField(fieldName);
        field.setAccessible(true);
        field.set(service, mock);
    }

    @AfterEach
    void tearDown() {
        mockedDataSourceSingleton.close();
        mockedPasswordHash.close();
    }

    // -----------------------------------------------------------
    // TEST: registrazione()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldRegisterClienteSuccessfully() {
        String email = "test@mail.com";
        String password = "Pwd123!";
        String nome = "Mario";
        String cognome = "Rossi";
        String hashedPwd = "hashedPassword";

        Map<String, String> inputs = new HashMap<>();
        inputs.put("email", email);
        inputs.put("password", password);
        inputs.put("nome", nome);
        inputs.put("cognome", cognome);

        // Validazione ok e utente non esistente
        when(validationManager.validate(inputs)).thenReturn(true);
        when(utenteDAO.retrieveByEmail(email)).thenReturn(null);
        mockedPasswordHash.when(() -> PasswordHash.hash(password)).thenReturn(hashedPwd);
        when(clienteDAO.create(any(Cliente.class))).thenReturn(true);

        Cliente result = service.registrazione(email, password, nome, cognome);

        assertNotNull(result);
        assertEquals(email, result.getEmail());
        assertEquals(hashedPwd, result.getPassword());
        assertEquals(nome, result.getNome());
        assertEquals(cognome, result.getCognome());
        verify(validationManager).validate(inputs);
        verify(clienteDAO).create(any(Cliente.class));
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenValidationFails() {
        String email = "invalid";
        String password = "short";
        String nome = "Mario";
        String cognome = "Rossi";

        Map<String, String> inputs = new HashMap<>();
        inputs.put("email", email);
        inputs.put("password", password);
        inputs.put("nome", nome);
        inputs.put("cognome", cognome);

        when(validationManager.validate(inputs)).thenReturn(false);

        Cliente result = service.registrazione(email, password, nome, cognome);

        assertNull(result);
        verify(validationManager).validate(inputs);
        verifyNoInteractions(clienteDAO);
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenUserAlreadyExists() {
        String email = "existing@mail.com";
        String password = "Pwd123!";
        String nome = "Mario";
        String cognome = "Rossi";

        Map<String, String> inputs = new HashMap<>();
        inputs.put("email", email);
        inputs.put("password", password);
        inputs.put("nome", nome);
        inputs.put("cognome", cognome);

        when(validationManager.validate(inputs)).thenReturn(true);
        when(utenteDAO.retrieveByEmail(email)).thenReturn(new Cliente(email, "pwd", nome, cognome));

        Cliente result = service.registrazione(email, password, nome, cognome);

        assertNull(result);
        verify(validationManager).validate(inputs);
        verify(utenteDAO).retrieveByEmail(email);
        verifyNoInteractions(clienteDAO);
    }

    @RepeatedTest(5)
    void shouldThrowRuntimeExceptionWhenPasswordHashFails() {
        String email = "test@mail.com";
        String password = "Pwd123!";
        String nome = "Mario";
        String cognome = "Rossi";

        Map<String, String> inputs = new HashMap<>();
        inputs.put("email", email);
        inputs.put("password", password);
        inputs.put("nome", nome);
        inputs.put("cognome", cognome);

        when(validationManager.validate(inputs)).thenReturn(true);
        when(utenteDAO.retrieveByEmail(email)).thenReturn(null);

        mockedPasswordHash.when(() -> PasswordHash.hash(password))
                .thenThrow(new RuntimeException("Errore hash"));

        assertThrows(RuntimeException.class, () ->
                service.registrazione(email, password, nome, cognome)
        );
    }



    @RepeatedTest(5)
    void shouldReturnNullWhenClienteDAOCreationFails() {
        String email = "fail@mail.com";
        String password = "Pwd123!";
        String nome = "Mario";
        String cognome = "Rossi";
        String hashed = "hashedPassword";

        Map<String, String> inputs = new HashMap<>();
        inputs.put("email", email);
        inputs.put("password", password);
        inputs.put("nome", nome);
        inputs.put("cognome", cognome);

        when(validationManager.validate(inputs)).thenReturn(true);
        when(utenteDAO.retrieveByEmail(email)).thenReturn(null);
        mockedPasswordHash.when(() -> PasswordHash.hash(password)).thenReturn(hashed);
        when(clienteDAO.create(any(Cliente.class))).thenReturn(false); // creazione fallita

        Cliente result = service.registrazione(email, password, nome, cognome);

        assertNotNull(result);
        verify(clienteDAO).create(any(Cliente.class));
    }
}
