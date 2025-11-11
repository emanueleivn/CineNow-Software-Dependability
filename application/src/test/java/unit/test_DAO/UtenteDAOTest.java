package unit.test_DAO;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.UtenteDAO;
import it.unisa.application.model.entity.Utente;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.*;
import org.mockito.junit.jupiter.MockitoExtension;

import javax.sql.DataSource;
import java.sql.*;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;
/**
 * Test di unità per UtenteDAO.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class UtenteDAOTest {

    @Mock
    private DataSource dataSource;

    @Mock
    private Connection connection;

    @Mock
    private PreparedStatement preparedStatement;

    @Mock
    private ResultSet resultSet;

    private UtenteDAO utenteDAO;

    private MockedStatic<DataSourceSingleton> mockedDataSourceSingleton;

    @BeforeEach
    void setUp() throws Exception {
        // Mock dello statico DataSourceSingleton.getInstance()
        mockedDataSourceSingleton = mockStatic(DataSourceSingleton.class);
        mockedDataSourceSingleton.when(DataSourceSingleton::getInstance).thenReturn(dataSource);

        lenient().when(dataSource.getConnection()).thenReturn(connection);

        // Istanzia il DAO normalmente — userà il singleton mockato
        utenteDAO = new UtenteDAO();
    }

    @AfterEach
    void tearDown() {
        mockedDataSourceSingleton.close();
    }

    // ------------------- TEST CREATE -------------------

    @RepeatedTest(5)
    void shouldReturnTrueWhenCreateSucceeds() throws Exception {
        Utente utente = new Utente("test@example.com", "password123", "ADMIN");
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);

        boolean result = utenteDAO.create(utente);

        assertTrue(result);
        verify(connection).prepareStatement(startsWith("INSERT"));
        verify(preparedStatement).setString(1, "test@example.com");
        verify(preparedStatement).setString(2, "password123");
        verify(preparedStatement).setString(3, "ADMIN");
        verify(preparedStatement).executeUpdate();
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenSQLExceptionThrownDuringCreate() throws Exception {
        Utente utente = new Utente("test@example.com", "password123", "ADMIN");
        when(connection.prepareStatement(anyString())).thenThrow(new SQLException());

        boolean result = utenteDAO.create(utente);

        assertFalse(result);
        verify(connection).prepareStatement(anyString());
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenExecuteUpdateReturnsZero() throws Exception {
        Utente utente = new Utente("test@example.com", "password123", "ADMIN");
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(0);

        boolean result = utenteDAO.create(utente);

        assertFalse(result);
        verify(preparedStatement).executeUpdate();
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenUserIsNull() {
        boolean success = utenteDAO.create(null);
        assertFalse(success, "Il metodo create() deve restituire false se l'utente è null");
    }
    // ------------------- TEST RETRIEVE -------------------

    @RepeatedTest(5)
    void shouldReturnUtenteWhenEmailExists() throws Exception {
        String email = "existing@example.com";
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true);
        when(resultSet.getString("password")).thenReturn("secret");
        when(resultSet.getString("ruolo")).thenReturn("USER");

        Utente result = utenteDAO.retrieveByEmail(email);

        assertNotNull(result);
        assertEquals(email, result.getEmail());
        assertEquals("secret", result.getPassword());
        assertEquals("USER", result.getRuolo());
        verify(connection).prepareStatement(startsWith("SELECT"));
        verify(preparedStatement).setString(1, email);
        verify(preparedStatement).executeQuery();
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenEmailNotFound() throws Exception {
        String email = "notfound@example.com";
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(false);

        Utente result = utenteDAO.retrieveByEmail(email);

        assertNull(result);
        verify(preparedStatement).setString(1, email);
        verify(resultSet).next();
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenSQLExceptionThrownDuringRetrieve() throws Exception {
        String email = "error@example.com";
        when(connection.prepareStatement(anyString())).thenThrow(new SQLException("DB error"));

        Utente result = utenteDAO.retrieveByEmail(email);

        assertNull(result);
        verify(connection).prepareStatement(anyString());
    }
}
