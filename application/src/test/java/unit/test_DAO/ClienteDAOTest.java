package unit.test_DAO;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.ClienteDAO;
import it.unisa.application.model.dao.UtenteDAO;
import it.unisa.application.model.dao.PrenotazioneDAO;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.model.entity.Prenotazione;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.MockedConstruction;
import org.mockito.MockedStatic;
import org.mockito.junit.jupiter.MockitoExtension;

import javax.sql.DataSource;
import java.sql.*;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test di unità per ClienteDAO.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class ClienteDAOTest {

    @Mock
    private DataSource mockDataSource;

    @Mock
    private Connection mockConnection;

    @Mock
    private PreparedStatement mockPreparedStatement;

    @Mock
    private ResultSet mockResultSet;

    private MockedStatic<DataSourceSingleton> mockedDataSourceSingleton;

    @BeforeEach
    void setUp() throws Exception {
        // Mock statico di DataSourceSingleton.getInstance()
        mockedDataSourceSingleton = mockStatic(DataSourceSingleton.class);
        mockedDataSourceSingleton.when(DataSourceSingleton::getInstance).thenReturn(mockDataSource);

        lenient().when(mockDataSource.getConnection()).thenReturn(mockConnection);
    }

    @AfterEach
    void tearDown() {
        mockedDataSourceSingleton.close();

    }

    // -----------------------------------------------------------
    // Test del metodo create()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldCreateClienteSuccessfully(RepetitionInfo repetitionInfo) throws Exception {
        Cliente cliente = new Cliente("cliente@mail.com", "pwd", "Mario", "Rossi");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);
        doNothing().when(mockConnection).commit();

        // Mock della new UtenteDAO() all’interno del metodo
        try (MockedConstruction<UtenteDAO> mockedUtenteDAO = mockConstruction(
                UtenteDAO.class,
                (mock, context) -> when(mock.create(any())).thenReturn(true)
        )) {
            ClienteDAO dao = new ClienteDAO();
            boolean result = dao.create(cliente);

            assertTrue(result, "create() deve restituire true (repetition " + repetitionInfo.getCurrentRepetition() + ")");
            verify(mockConnection).commit();
            verify(mockPreparedStatement, atLeast(1)).executeUpdate();

            // Verifica che sia stata creata almeno un'istanza di UtenteDAO
            assertEquals(1, mockedUtenteDAO.constructed().size());
        }
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenSQLExceptionDuringInsert(RepetitionInfo repetitionInfo) throws Exception {
        Cliente cliente = new Cliente("cliente@mail.com", "pwd", "Mario", "Rossi");
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenThrow(new SQLException("Errore SQL"));
        doNothing().when(mockConnection).rollback();
        ClienteDAO dao = new ClienteDAO();
        boolean result = dao.create(cliente);

        assertFalse(result, "create() deve restituire false in caso di SQLException (repetition " + repetitionInfo.getCurrentRepetition() + ")");
        verify(mockConnection).rollback();

    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenConnectionFails() throws Exception {
        mockedDataSourceSingleton.close();
        mockedDataSourceSingleton = mockStatic(DataSourceSingleton.class);
        mockedDataSourceSingleton.when(DataSourceSingleton::getInstance).thenReturn(mockDataSource);
        when(mockDataSource.getConnection()).thenThrow(new SQLException());

        Cliente cliente = new Cliente("cliente@mail.com", "pwd", "Mario", "Rossi");
        ClienteDAO dao = new ClienteDAO();

        boolean result = dao.create(cliente);

        assertFalse(result);
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenUserIsNull() {
        ClienteDAO dao = new ClienteDAO();
        boolean success = dao.create(null);
        assertFalse(success, "Il metodo create() deve restituire false se il cliente è null");
    }
    // -----------------------------------------------------------
    // Test del metodo retrieveByEmail()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnClienteWhenFound() throws Exception {
        String email = "cliente@mail.com";
        String password = "pwd";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getString("nome")).thenReturn("Mario");
        when(mockResultSet.getString("cognome")).thenReturn("Rossi");

        List<Prenotazione> mockPrenotazioni = Collections.emptyList();

        // Mock della new PrenotazioneDAO() all’interno del metodo
        try (MockedConstruction<PrenotazioneDAO> mockedPrenotazioneDAO = mockConstruction(
                PrenotazioneDAO.class,
                (mock, context) -> when(mock.retrieveAllByCliente(any())).thenReturn(mockPrenotazioni)
        )) {
            ClienteDAO dao = new ClienteDAO();
            Cliente result = dao.retrieveByEmail(email, password);

            assertNotNull(result);
            assertEquals(email, result.getEmail());
            assertEquals("Mario", result.getNome());
            assertEquals("Rossi", result.getCognome());
            assertEquals(mockPrenotazioni, result.storicoOrdini());

            // Verifica che PrenotazioneDAO sia stato istanziato
            assertEquals(1, mockedPrenotazioneDAO.constructed().size());
        }
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenNoResultFound() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        ClienteDAO dao = new ClienteDAO();
        Cliente result = dao.retrieveByEmail("notfound@mail.com", "pwd");

        assertNull(result);
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenSQLExceptionOccurs() throws Exception {
        when(mockDataSource.getConnection()).thenThrow(new SQLException());

        ClienteDAO dao = new ClienteDAO();
        Cliente result = dao.retrieveByEmail("error@mail.com", "pwd");

        assertNull(result);
    }
}
