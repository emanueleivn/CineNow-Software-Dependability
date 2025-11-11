package unit.test_DAO;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.FilmDAO;
import it.unisa.application.model.entity.Film;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.*;
import org.mockito.junit.jupiter.MockitoExtension;

import javax.sql.DataSource;
import java.sql.*;
import java.util.*;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test di unità per FilmDAO.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class FilmDAOTest {

    @Mock
    private DataSource mockDataSource;
    @Mock
    private Connection mockConnection;
    @Mock
    private PreparedStatement mockPreparedStatement;
    @Mock
    private Statement mockStatement;
    @Mock
    private ResultSet mockResultSet;

    private MockedStatic<DataSourceSingleton> mockedDataSourceSingleton;

    @BeforeEach
    void setUp() throws Exception {
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
    void shouldCreateFilmSuccessfully() throws Exception {
        Film film = new Film(0, "Titolo", "Genere", "PG", 120, new byte[]{1, 2, 3}, "Descrizione", true);

        when(mockConnection.prepareStatement(anyString(), (int) eq(Statement.RETURN_GENERATED_KEYS)))
                .thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        ResultSet mockKeys = mock(ResultSet.class);
        when(mockPreparedStatement.getGeneratedKeys()).thenReturn(mockKeys);
        when(mockKeys.next()).thenReturn(true);
        when(mockKeys.getInt(1)).thenReturn(10);

        FilmDAO dao = new FilmDAO();
        boolean result = dao.create(film);

        assertTrue(result);
        assertEquals(10, film.getId());
        verify(mockPreparedStatement).setString(1, "Titolo");
        verify(mockPreparedStatement).setBoolean(7, true);
        verify(mockPreparedStatement).executeUpdate();
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenSQLExceptionOccursInCreate() throws Exception {
        Film film = new Film(0, "Titolo", "Genere", "PG", 120, null, "Descrizione", true);
        when(mockConnection.prepareStatement(anyString(), (int) eq(Statement.RETURN_GENERATED_KEYS)))
                .thenThrow(new SQLException());

        FilmDAO dao = new FilmDAO();
        boolean result = dao.create(film);

        assertFalse(result);
        verify(mockDataSource).getConnection();
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenExecuteUpdateReturnsZero() throws Exception {
        Film film = new Film(0, "Titolo", "Genere", "PG", 120, null, "Descrizione", true);

        when(mockConnection.prepareStatement(anyString(), (int) eq(Statement.RETURN_GENERATED_KEYS)))
                .thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        FilmDAO dao = new FilmDAO();
        boolean result = dao.create(film);

        assertFalse(result);
        verify(mockPreparedStatement).executeUpdate();
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenUserIsNull() {
        FilmDAO dao = new FilmDAO();
        boolean success = dao.create(null);
        assertFalse(success, "Il metodo create() deve restituire false se il film è null");
    }
    // -----------------------------------------------------------
    // Test del metodo retrieveById()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnFilmWhenFound() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt("id")).thenReturn(1);
        when(mockResultSet.getString("titolo")).thenReturn("Matrix");
        when(mockResultSet.getString("genere")).thenReturn("Sci-Fi");
        when(mockResultSet.getString("classificazione")).thenReturn("PG");
        when(mockResultSet.getInt("durata")).thenReturn(136);
        when(mockResultSet.getBytes("locandina")).thenReturn(new byte[]{1});
        when(mockResultSet.getString("descrizione")).thenReturn("Film cult");
        when(mockResultSet.getBoolean("is_proiettato")).thenReturn(true);

        FilmDAO dao = new FilmDAO();
        Film result = dao.retrieveById(1);

        assertNotNull(result);
        assertEquals("Matrix", result.getTitolo());
        assertEquals("Sci-Fi", result.getGenere());
        assertTrue(result.isProiettato());
        verify(mockPreparedStatement).setInt(1, 1);
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenFilmNotFound() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        FilmDAO dao = new FilmDAO();
        Film result = dao.retrieveById(99);

        assertNull(result);
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenSQLExceptionOccursInRetrieveById() throws Exception {
        when(mockDataSource.getConnection()).thenThrow(new SQLException());

        FilmDAO dao = new FilmDAO();
        Film result = dao.retrieveById(1);

        assertNull(result);
    }

    // -----------------------------------------------------------
    // Test del metodo retrieveAll()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnAllFilmsSuccessfully() throws Exception {
        when(mockConnection.createStatement()).thenReturn(mockStatement);
        when(mockStatement.executeQuery(anyString())).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, false);

        when(mockResultSet.getInt("id")).thenReturn(1, 2);
        when(mockResultSet.getString("titolo")).thenReturn("Film1", "Film2");
        when(mockResultSet.getString("genere")).thenReturn("Action", "Comedy");
        when(mockResultSet.getString("classificazione")).thenReturn("PG", "PG-13");
        when(mockResultSet.getInt("durata")).thenReturn(120, 90);
        when(mockResultSet.getBytes("locandina")).thenReturn(new byte[]{1}, new byte[]{2});
        when(mockResultSet.getString("descrizione")).thenReturn("Desc1", "Desc2");
        when(mockResultSet.getBoolean("is_proiettato")).thenReturn(true, false);

        FilmDAO dao = new FilmDAO();
        List<Film> result = dao.retrieveAll();

        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals("Film1", result.get(0).getTitolo());
        assertEquals("Film2", result.get(1).getTitolo());
        verify(mockConnection).createStatement();
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenSQLExceptionOccursInRetrieveAll() throws Exception {
        when(mockDataSource.getConnection()).thenThrow(new SQLException());

        FilmDAO dao = new FilmDAO();
        List<Film> result = dao.retrieveAll();

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenNoResults() throws Exception {
        when(mockConnection.createStatement()).thenReturn(mockStatement);
        when(mockStatement.executeQuery(anyString())).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        FilmDAO dao = new FilmDAO();
        List<Film> result = dao.retrieveAll();

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }
}
