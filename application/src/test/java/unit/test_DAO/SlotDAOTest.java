package unit.test_DAO;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.SlotDAO;
import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.model.entity.Slot;
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
 * Test di unità per la classe SlotDAO.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class SlotDAOTest {

    @Mock private DataSource mockDataSource;
    @Mock private Connection mockConnection;
    @Mock private PreparedStatement mockPreparedStatement;
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
    // TEST: retrieveById()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnSlotWhenIdExists() throws Exception {
        Time oraInizio = Time.valueOf("14:30:00");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getTime("ora_inizio")).thenReturn(oraInizio);

        SlotDAO dao = new SlotDAO();
        Slot result = dao.retrieveById(1);

        assertNotNull(result);
        assertEquals(1, result.getId());
        assertEquals(oraInizio, result.getOraInizio());
        verify(mockPreparedStatement).setInt(1, 1);
        verify(mockPreparedStatement).executeQuery();
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenSlotIdNotFound() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        SlotDAO dao = new SlotDAO();
        Slot result = dao.retrieveById(10);

        assertNull(result);
        verify(mockPreparedStatement).setInt(1, 10);
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenSQLExceptionOccursInRetrieveById() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException());

        SlotDAO dao = new SlotDAO();
        Slot result = dao.retrieveById(1);

        assertNull(result);
        verify(mockDataSource).getConnection();
    }

    // -----------------------------------------------------------
    // TEST: retrieveByProiezione()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnSlotWhenProiezioneHasValidSlot() throws Exception {
        Proiezione mockProiezione = mock(Proiezione.class);
        Slot mockSlot = new Slot(2, Time.valueOf("16:00:00"));
        when(mockProiezione.getOrarioProiezione()).thenReturn(mockSlot);

        Time oraInizio = Time.valueOf("16:00:00");
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt("id")).thenReturn(2);
        when(mockResultSet.getTime("ora_inizio")).thenReturn(oraInizio);

        SlotDAO dao = new SlotDAO();
        Slot result = dao.retrieveByProiezione(mockProiezione);

        assertNotNull(result);
        assertEquals(2, result.getId());
        assertEquals(oraInizio, result.getOraInizio());
        verify(mockPreparedStatement).setInt(1, 2);
        verify(mockPreparedStatement).executeQuery();
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenProiezioneIsNull() {
        SlotDAO dao = new SlotDAO();
        Slot result = dao.retrieveByProiezione(null);
        assertNull(result);
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenProiezioneSlotIsNull() {
        Proiezione mockProiezione = mock(Proiezione.class);
        when(mockProiezione.getOrarioProiezione()).thenReturn(null);

        SlotDAO dao = new SlotDAO();
        Slot result = dao.retrieveByProiezione(mockProiezione);

        assertNull(result);
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenSQLExceptionOccursInRetrieveByProiezione() throws Exception {
        Proiezione mockProiezione = mock(Proiezione.class);
        Slot mockSlot = new Slot(4, Time.valueOf("20:00:00"));

        when(mockProiezione.getOrarioProiezione()).thenReturn(mockSlot);

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException());

        SlotDAO dao = new SlotDAO();
        Slot result = dao.retrieveByProiezione(mockProiezione);

        assertNull(result);
        verify(mockDataSource).getConnection();
    }

    // -----------------------------------------------------------
    // TEST: retrieveAllSlots()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnListOfSlotsWhenQuerySucceeds() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

        when(mockResultSet.next()).thenReturn(true, true, false);
        when(mockResultSet.getInt("id")).thenReturn(1, 2);
        when(mockResultSet.getTime("ora_inizio"))
                .thenReturn(Time.valueOf("10:00:00"), Time.valueOf("12:00:00"));

        SlotDAO dao = new SlotDAO();
        List<Slot> result = dao.retrieveAllSlots();

        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals(Time.valueOf("10:00:00"), result.get(0).getOraInizio());
        assertEquals(Time.valueOf("12:00:00"), result.get(1).getOraInizio());
        verify(mockPreparedStatement).executeQuery();
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenNoResultsFound() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        SlotDAO dao = new SlotDAO();
        List<Slot> result = dao.retrieveAllSlots();

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenSQLExceptionOccursInRetrieveAllSlots() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException());

        SlotDAO dao = new SlotDAO();
        List<Slot> result = dao.retrieveAllSlots();

        assertNotNull(result);
        assertTrue(result.isEmpty());
        verify(mockDataSource).getConnection();
    }
}
