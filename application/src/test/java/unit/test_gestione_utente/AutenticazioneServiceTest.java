package unit.test_gestione_utente;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.ClienteDAO;
import it.unisa.application.model.dao.SedeDAO;
import it.unisa.application.model.dao.UtenteDAO;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.model.entity.GestoreSede;
import it.unisa.application.model.entity.Sede;
import it.unisa.application.model.entity.Utente;
import it.unisa.application.sottosistemi.gestione_utente.service.AutenticazioneService;
import it.unisa.application.utilities.PasswordHash;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.*;
import org.mockito.junit.jupiter.MockitoExtension;

import javax.sql.DataSource;
import java.lang.reflect.Field;
import java.sql.Connection;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test di unità per AutenticazioneService.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class AutenticazioneServiceTest {

    @Mock private UtenteDAO utenteDAO;
    @Mock private ClienteDAO clienteDAO;
    @Mock private SedeDAO sedeDAO;
    @Mock private HttpSession mockSession;

    @Mock private DataSource mockDataSource;
    @Mock private Connection mockConnection;

    private MockedStatic<DataSourceSingleton> mockedDataSourceSingleton;
    private MockedStatic<PasswordHash> mockedPasswordHash;

    private AutenticazioneService service;

    @BeforeEach
    void setUp() throws Exception {
        //  Mock statico per evitare connessioni reali
        mockedDataSourceSingleton = mockStatic(DataSourceSingleton.class);
        mockedDataSourceSingleton.when(DataSourceSingleton::getInstance).thenReturn(mockDataSource);
        lenient().when(mockDataSource.getConnection()).thenReturn(mockConnection);

        // Mock statico del PasswordHash
        mockedPasswordHash = mockStatic(PasswordHash.class);

        // Crea il service reale e sostituisci i DAO via reflection
        service = new AutenticazioneService();
        injectMock("utenteDAO", utenteDAO);
        injectMock("clienteDAO", clienteDAO);
    }

    private void injectMock(String fieldName, Object mock) throws Exception {
        Field field = AutenticazioneService.class.getDeclaredField(fieldName);
        field.setAccessible(true);
        field.set(service, mock);
    }

    @AfterEach
    void tearDown() {
        mockedDataSourceSingleton.close();
        mockedPasswordHash.close();
    }

    // -----------------------------------------------------------
    // TEST: login()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnNullWhenUserNotFound() {
        when(utenteDAO.retrieveByEmail("notfound@mail.com")).thenReturn(null);

        Utente result = service.login("notfound@mail.com", "pwd");

        assertNull(result);
        verify(utenteDAO).retrieveByEmail("notfound@mail.com");
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenPasswordIncorrect() {
        Utente user = new Utente("mail@test.com", "hashedPwd", "cliente");
        when(utenteDAO.retrieveByEmail("mail@test.com")).thenReturn(user);
        mockedPasswordHash.when(() -> PasswordHash.hash("wrongpwd")).thenReturn("differentHash");

        Utente result = service.login("mail@test.com", "wrongpwd");

        assertNull(result);
        verify(utenteDAO).retrieveByEmail("mail@test.com");
        verifyNoInteractions(clienteDAO);
    }

    @RepeatedTest(5)
    void shouldReturnClienteWhenCredentialsCorrectAndRoleCliente() {
        String email = "cliente@mail.com";
        String plainPwd = "pwd";
        String hashed = "hashedPwd";
        Utente base = new Utente(email, hashed, "cliente");

        when(utenteDAO.retrieveByEmail(email)).thenReturn(base);
        mockedPasswordHash.when(() -> PasswordHash.hash(plainPwd)).thenReturn(hashed);

        Cliente cliente = new Cliente(email, hashed, "Mario", "Rossi");

        when(clienteDAO.retrieveByEmail(email, hashed)).thenReturn(cliente);

        Utente result = service.login(email, plainPwd);

        assertNotNull(result);
        assertInstanceOf(Cliente.class, result); // verifica tipo specifico
        assertEquals(email, result.getEmail());
        assertEquals("cliente", result.getRuolo());
        verify(clienteDAO).retrieveByEmail(email, hashed);
    }


    @RepeatedTest(5)
    void shouldReturnGestoreSedeWhenRoleIsGestoreSede() {
        String email = "gestore@mail.com";
        String plainPwd = "pwd";
        String hashed = "hashedPwd";
        Utente base = new Utente(email, hashed, "gestore_sede");

        when(utenteDAO.retrieveByEmail(email)).thenReturn(base);
        mockedPasswordHash.when(() -> PasswordHash.hash(plainPwd)).thenReturn(hashed);

        Sede sede = new Sede(1, "Sede Test", "Via Roma");
        try (MockedConstruction<SedeDAO> mockedSedeDAO = mockConstruction(SedeDAO.class,
                (mock, context) -> when(mock.retrieveByGestoreEmail(email)).thenReturn(sede))) {

            Utente result = service.login(email, plainPwd);

            assertNotNull(result);
            assertInstanceOf(GestoreSede.class, result);
            GestoreSede gs = (GestoreSede) result;
            assertEquals(email, gs.getEmail());
            assertEquals(sede, gs.getSede());
            assertEquals("gestore_sede", gs.getRuolo());
            verify(mockedSedeDAO.constructed().getFirst()).retrieveByGestoreEmail(email);
        }
    }

    @RepeatedTest(5)
    void shouldReturnBaseUserWhenRoleIsDifferent() {
        String email = "admin@mail.com";
        String hashed = "hashedPwd";
        Utente base = new Utente(email, hashed, "admin");

        when(utenteDAO.retrieveByEmail(email)).thenReturn(base);
        mockedPasswordHash.when(() -> PasswordHash.hash("pwd")).thenReturn(hashed);

        Utente result = service.login(email, "pwd");

        assertNotNull(result);
        assertEquals("admin", result.getRuolo());
        assertEquals(email, result.getEmail());
    }

    // -----------------------------------------------------------
    // TEST: logout()
    // -----------------------------------------------------------

    @Test
    void shouldInvalidateSessionOnLogout() {
        service.logout(mockSession);
        verify(mockSession).invalidate();
    }
}
