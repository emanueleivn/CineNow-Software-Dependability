package unit.test_DAO;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.SalaDAO;
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
 * Test di unità per SalaDAO.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class SalaDAOTest {

    @Mock private DataSource mockDataSource;
    @Mock private Connection mockConnection;
    @Mock private PreparedStatement mockPreparedStatement;
    @Mock private ResultSet mockResultSet;

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
    void shouldReturnSalaWhenIdExists(RepetitionInfo info) throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt("numero")).thenReturn(2);
        when(mockResultSet.getInt("capienza")).thenReturn(150);
        when(mockResultSet.getInt("id_sede")).thenReturn(5);

        SalaDAO dao = new SalaDAO();
        Sala result = dao.retrieveById(1);

        assertNotNull(result);
        assertEquals(2, result.getNumeroSala());
        assertEquals(150, result.getCapienza());
        assertEquals(5, result.getSede().getId());
        verify(mockPreparedStatement).setInt(1, 1);
        verify(mockPreparedStatement).executeQuery();
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenIdNotFound(RepetitionInfo info) throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        SalaDAO dao = new SalaDAO();
        Sala result = dao.retrieveById(99);

        assertNull(result);
        verify(mockPreparedStatement).setInt(1, 99);
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenSQLExceptionOccursInRetrieveById(RepetitionInfo info) throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("DB error"));

        SalaDAO dao = new SalaDAO();
        Sala result = dao.retrieveById(1);

        assertNull(result);
        verify(mockDataSource).getConnection();
    }

    // -----------------------------------------------------------
    // Test del metodo retrieveAll()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnListOfSalaWhenQuerySucceeds(RepetitionInfo info) throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, false);

        when(mockResultSet.getInt("id")).thenReturn(1, 2);
        when(mockResultSet.getInt("numero")).thenReturn(3, 4);
        when(mockResultSet.getInt("capienza")).thenReturn(100, 200);
        when(mockResultSet.getInt("id_sede")).thenReturn(10, 20);

        SalaDAO dao = new SalaDAO();
        List<Sala> result = dao.retrieveAll();

        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals(3, result.get(0).getNumeroSala());
        assertEquals(4, result.get(1).getNumeroSala());
        verify(mockPreparedStatement).executeQuery();
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenNoResultsFound(RepetitionInfo info) throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        SalaDAO dao = new SalaDAO();
        List<Sala> result = dao.retrieveAll();

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @RepeatedTest(5)
    void shouldThrowSQLExceptionWhenQueryFails(RepetitionInfo info) throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Query failed"));

        SalaDAO dao = new SalaDAO();
        assertThrows(SQLException.class, dao::retrieveAll);
        verify(mockDataSource).getConnection();
    }
}
