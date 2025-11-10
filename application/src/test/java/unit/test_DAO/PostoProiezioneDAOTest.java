package unit.test_DAO;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.PostoProiezioneDAO;
import it.unisa.application.model.dao.PrenotazioneDAO;
import it.unisa.application.model.entity.*;
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
 * Test di unità per PostoProiezioneDAO.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class PostoProiezioneDAOTest {

    @Mock private DataSource mockDataSource;
    @Mock private Connection mockConnection;
    @Mock private PreparedStatement mockPreparedStatement;
    @Mock private PreparedStatement mockPreparedStatement2;
    @Mock private ResultSet mockResultSet;

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
    void shouldCreatePostoProiezioneSuccessfully(RepetitionInfo info) throws Exception {
        Sala sala = new Sala(1, 1, 100, null);
        Posto posto = new Posto(sala, 'A', 5);
        Proiezione proiezione = new Proiezione(10);
        PostoProiezione postoProiezione = new PostoProiezione(posto, proiezione);
        postoProiezione.setStato(true);

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        PostoProiezioneDAO dao = new PostoProiezioneDAO();
        boolean result = dao.create(postoProiezione);

        assertTrue(result);
        verify(mockPreparedStatement).setInt(1, sala.getId());
        verify(mockPreparedStatement).setString(2, String.valueOf(posto.getFila()));
        verify(mockPreparedStatement).setInt(3, posto.getNumero());
        verify(mockPreparedStatement).setInt(4, proiezione.getId());
        verify(mockPreparedStatement).setBoolean(5, true);
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenSQLExceptionOccursInCreate(RepetitionInfo info) throws Exception {
        Sala sala = new Sala(1, 1, 100, null);
        Posto posto = new Posto(sala, 'A', 5);
        Proiezione proiezione = new Proiezione(10);
        PostoProiezione postoProiezione = new PostoProiezione(posto, proiezione);

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("DB error"));

        PostoProiezioneDAO dao = new PostoProiezioneDAO();
        boolean result = dao.create(postoProiezione);

        assertFalse(result);
        verify(mockDataSource).getConnection();
    }
    @RepeatedTest(5)
    void shouldReturnFalseWhenPostoProiezioneIsNull() {
        PostoProiezioneDAO dao = new PostoProiezioneDAO();
        boolean success = dao.create(null);
        assertFalse(success, "Il metodo create() deve restituire false se il postoProiezione è null");
    }

    // -----------------------------------------------------------
    // Test del metodo retrieveAllByProiezione()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnListOfPostiProiezioneWhenFound(RepetitionInfo info) throws Exception {
        Proiezione proiezione = new Proiezione(7);

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

        when(mockResultSet.next()).thenReturn(true, true, false);
        when(mockResultSet.getInt("id_sala")).thenReturn(1, 2);
        when(mockResultSet.getString("fila")).thenReturn("A", "B");
        when(mockResultSet.getInt("numero")).thenReturn(5, 6);
        when(mockResultSet.getBoolean("stato")).thenReturn(true, false);

        PostoProiezioneDAO dao = new PostoProiezioneDAO();
        List<PostoProiezione> result = dao.retrieveAllByProiezione(proiezione);

        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals('A', result.get(0).getPosto().getFila());
        assertEquals('B', result.get(1).getPosto().getFila());
        assertEquals(5, result.get(0).getPosto().getNumero());
        verify(mockPreparedStatement).setInt(1, proiezione.getId());
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenNoResults(RepetitionInfo info) throws Exception {
        Proiezione proiezione = new Proiezione(7);

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        PostoProiezioneDAO dao = new PostoProiezioneDAO();
        List<PostoProiezione> result = dao.retrieveAllByProiezione(proiezione);

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenSQLExceptionOccurs(RepetitionInfo info) throws Exception {
        Proiezione proiezione = new Proiezione(7);
        when(mockDataSource.getConnection()).thenThrow(new SQLException("Connessione fallita"));

        PostoProiezioneDAO dao = new PostoProiezioneDAO();
        List<PostoProiezione> result = dao.retrieveAllByProiezione(proiezione);

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    // -----------------------------------------------------------
    // Test del metodo occupaPosto()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldOccupySeatSuccessfully(RepetitionInfo info) throws Exception {
        Sala sala = new Sala(1, 1, 100, null);
        Posto posto = new Posto(sala, 'A', 5);
        Proiezione proiezione = new Proiezione(3);
        PostoProiezione postoProiezione = new PostoProiezione(posto, proiezione);

        when(mockConnection.prepareStatement(contains("UPDATE"))).thenReturn(mockPreparedStatement);
        when(mockConnection.prepareStatement(contains("INSERT"))).thenReturn(mockPreparedStatement2);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);
        when(mockPreparedStatement2.executeUpdate()).thenReturn(1);

        PostoProiezioneDAO dao = new PostoProiezioneDAO();
        boolean result = dao.occupaPosto(postoProiezione, 99);

        assertTrue(result);
        verify(mockPreparedStatement).setInt(1, sala.getId());
        verify(mockPreparedStatement2).setInt(5, 99);
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenUpdateFailsInOccupaPosto(RepetitionInfo info) throws Exception {
        Sala sala = new Sala(1, 1, 100, null);
        Posto posto = new Posto(sala, 'A', 5);
        Proiezione proiezione = new Proiezione(3);
        PostoProiezione postoProiezione = new PostoProiezione(posto, proiezione);

        when(mockConnection.prepareStatement(contains("UPDATE"))).thenReturn(mockPreparedStatement);
        when(mockConnection.prepareStatement(contains("INSERT"))).thenReturn(mockPreparedStatement2);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        PostoProiezioneDAO dao = new PostoProiezioneDAO();
        boolean result = dao.occupaPosto(postoProiezione, 99);

        assertFalse(result);
        verify(mockPreparedStatement).executeUpdate();
        verify(mockPreparedStatement2, never()).executeUpdate();
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenSQLExceptionOccursInOccupaPosto(RepetitionInfo info) throws Exception {
        Sala sala = new Sala(1, 1, 100, null);
        Posto posto = new Posto(sala, 'A', 5);
        Proiezione proiezione = new Proiezione(3);
        PostoProiezione postoProiezione = new PostoProiezione(posto, proiezione);

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Errore SQL"));

        PostoProiezioneDAO dao = new PostoProiezioneDAO();
        boolean result = dao.occupaPosto(postoProiezione, 99);

        assertFalse(result);
        verify(mockDataSource).getConnection();
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenProiezioneIsNull() {
        PostoProiezioneDAO dao = new PostoProiezioneDAO();
        List<PostoProiezione> result = dao.retrieveAllByProiezione(null);
        assertNull(result);
    }
}
