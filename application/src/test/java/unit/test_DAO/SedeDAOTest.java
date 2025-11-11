package unit.test_DAO;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.SedeDAO;
import it.unisa.application.model.entity.Film;
import it.unisa.application.model.entity.Sala;
import it.unisa.application.model.entity.Sede;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.*;
import org.mockito.junit.jupiter.MockitoExtension;

import javax.sql.DataSource;
import java.sql.*;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test di unità per SedeDAO.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class SedeDAOTest {

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
        mockedDataSourceSingleton = mockStatic(DataSourceSingleton.class);
        mockedDataSourceSingleton.when(DataSourceSingleton::getInstance).thenReturn(mockDataSource);
        when(mockDataSource.getConnection()).thenReturn(mockConnection);
    }

    @AfterEach
    void tearDown() {
        mockedDataSourceSingleton.close();
    }

    // -----------------------------------------------------------
    // Test del metodo retrieveById()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnSedeWhenIdExists() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt("id")).thenReturn(1);
        when(mockResultSet.getString("nome")).thenReturn("Cinema Star");
        when(mockResultSet.getString("via")).thenReturn("Via Roma");
        when(mockResultSet.getString("citta")).thenReturn("Napoli");
        when(mockResultSet.getString("cap")).thenReturn("80100");

        SedeDAO dao = new SedeDAO();
        Sede result = dao.retrieveById(1);

        assertNotNull(result);
        assertEquals(1, result.getId());
        assertEquals("Cinema Star", result.getNome());
        assertTrue(result.getIndirizzo().contains("Via Roma"));
        verify(mockPreparedStatement).setInt(1, 1);
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenIdNotFound() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        SedeDAO dao = new SedeDAO();
        Sede result = dao.retrieveById(99);

        assertNull(result);
        verify(mockPreparedStatement).setInt(1, 99);
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenSQLExceptionOccursInRetrieveById() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException());

        SedeDAO dao = new SedeDAO();
        Sede result = dao.retrieveById(1);

        assertNull(result);
        verify(mockDataSource).getConnection();
    }

    // -----------------------------------------------------------
    // Test del metodo retrieveAll()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnListOfSediWhenQuerySucceeds() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, false);

        when(mockResultSet.getInt("id")).thenReturn(1, 2);
        when(mockResultSet.getString("nome")).thenReturn("Cinema Uno", "Cinema Due");
        when(mockResultSet.getString("via")).thenReturn("Via Napoli", "Via Roma");
        when(mockResultSet.getString("citta")).thenReturn("Salerno", "Avellino");
        when(mockResultSet.getString("cap")).thenReturn("84100", "83100");

        SedeDAO dao = new SedeDAO();
        List<Sede> result = dao.retrieveAll();

        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals("Cinema Uno", result.get(0).getNome());
        assertTrue(result.get(1).getIndirizzo().contains("Via Roma"));
        verify(mockPreparedStatement).executeQuery();
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenNoResultsFound() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        SedeDAO dao = new SedeDAO();
        List<Sede> result = dao.retrieveAll();

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenSQLExceptionOccursInRetrieveAll() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException());

        SedeDAO dao = new SedeDAO();
        List<Sede> result = dao.retrieveAll();

        assertNotNull(result);
        assertTrue(result.isEmpty());
        verify(mockDataSource).getConnection();
    }

    // -----------------------------------------------------------
    // Test del metodo retrieveSaleBySede()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnListOfSaleForGivenSede() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getInt("id")).thenReturn(1);
        when(mockResultSet.getInt("numero")).thenReturn(5);
        when(mockResultSet.getInt("capienza")).thenReturn(150);

        SedeDAO dao = new SedeDAO();
        List<Sala> result = dao.retrieveSaleBySede(10);

        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals(5, result.getFirst().getNumeroSala());
        assertEquals(150, result.getFirst().getCapienza());
        verify(mockPreparedStatement).setInt(1, 10);
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenSQLExceptionOccursInRetrieveSaleBySede() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException());

        SedeDAO dao = new SedeDAO();
        List<Sala> result = dao.retrieveSaleBySede(10);

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    // -----------------------------------------------------------
    // Test del metodo retrieveByGestoreEmail()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnSedeWhenGestoreEmailExists() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt("id")).thenReturn(7);
        when(mockResultSet.getString("nome")).thenReturn("Cinema Gestore");
        when(mockResultSet.getString("via")).thenReturn("Via Milano");
        when(mockResultSet.getString("citta")).thenReturn("Roma");
        when(mockResultSet.getString("cap")).thenReturn("00100");

        SedeDAO dao = new SedeDAO();
        Sede result = dao.retrieveByGestoreEmail("gestore@cinema.it");

        assertNotNull(result);
        assertEquals(7, result.getId());
        assertEquals("Cinema Gestore", result.getNome());
        assertTrue(result.getIndirizzo().contains("Via Milano"));
        verify(mockPreparedStatement).setString(1, "gestore@cinema.it");
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenNoGestoreFound() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        SedeDAO dao = new SedeDAO();
        Sede result = dao.retrieveByGestoreEmail("non@esiste.it");

        assertNull(result);
        verify(mockPreparedStatement).setString(1, "non@esiste.it");
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenSQLExceptionOccursInRetrieveByGestoreEmail() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException());

        SedeDAO dao = new SedeDAO();
        Sede result = dao.retrieveByGestoreEmail("gestore@cinema.it");

        assertNull(result);
        verify(mockDataSource).getConnection();
    }

    // -----------------------------------------------------------
    // Test del metodo retrieveFilm()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnListOfFilmForSede() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, false);

        when(mockResultSet.getInt("id")).thenReturn(1, 2);
        when(mockResultSet.getString("titolo")).thenReturn("Film A", "Film B");
        when(mockResultSet.getString("genere")).thenReturn("Azione", "Commedia");
        when(mockResultSet.getString("classificazione")).thenReturn("PG", "PG-13");
        when(mockResultSet.getInt("durata")).thenReturn(120, 90);
        when(mockResultSet.getBytes("locandina")).thenReturn(new byte[]{1, 2}, new byte[]{3, 4});
        when(mockResultSet.getString("descrizione")).thenReturn("Descrizione A", "Descrizione B");
        when(mockResultSet.getBoolean("is_proiettato")).thenReturn(true, false);

        SedeDAO dao = new SedeDAO();
        List<Film> result = dao.retrieveFilm(5);

        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals("Film A", result.get(0).getTitolo());
        assertEquals("Film B", result.get(1).getTitolo());
        verify(mockPreparedStatement).setInt(1, 5);
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenSQLExceptionOccursInRetrieveFilm() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException());

        SedeDAO dao = new SedeDAO();
        List<Film> result = dao.retrieveFilm(10);

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }
}
