package unit.test_DAO;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.*;
import it.unisa.application.model.entity.*;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.*;
import org.mockito.junit.jupiter.MockitoExtension;

import javax.sql.DataSource;
import java.sql.*;
import java.sql.Date;
import java.time.LocalDate;
import java.util.*;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test di unità per PrenotazioneDAO con mock statici e costruttivi.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class PrenotazioneDAOTest {

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
    void shouldCreatePrenotazioneSuccessfully(RepetitionInfo info) throws Exception {
        Cliente cliente = new Cliente("mail@test.com", "pwd", "Mario", "Rossi");
        Proiezione proiezione = new Proiezione(1);
        Prenotazione prenotazione = new Prenotazione(0, cliente, proiezione);

        when(mockConnection.prepareStatement(anyString(), anyInt())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        ResultSet mockKeys = mock(ResultSet.class);
        when(mockPreparedStatement.getGeneratedKeys()).thenReturn(mockKeys);
        when(mockKeys.next()).thenReturn(true);
        when(mockKeys.getInt(1)).thenReturn(42);

        PrenotazioneDAO dao = new PrenotazioneDAO();
        boolean result = dao.create(prenotazione);

        assertTrue(result);
        assertEquals(42, prenotazione.getId());
        verify(mockPreparedStatement).setString(1, "mail@test.com");
        verify(mockPreparedStatement).setInt(2, 1);
        verify(mockPreparedStatement).executeUpdate();
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenSQLExceptionInCreate(RepetitionInfo info) throws Exception {
        Cliente cliente = new Cliente("mail@test.com", "pwd", "Mario", "Rossi");
        Proiezione proiezione = new Proiezione(1);
        Prenotazione prenotazione = new Prenotazione(0, cliente, proiezione);

        when(mockConnection.prepareStatement(anyString(), anyInt())).thenThrow(new SQLException("DB error"));

        PrenotazioneDAO dao = new PrenotazioneDAO();
        boolean result = dao.create(prenotazione);

        assertFalse(result);
        verify(mockDataSource).getConnection();
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenPrenotazioneIsNull() {
        PrenotazioneDAO dao = new PrenotazioneDAO();
        boolean result = dao.create(null);
        assertFalse(result);
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenClienteOrProiezioneIsNull() {
        PrenotazioneDAO dao = new PrenotazioneDAO();

        // Caso 1: cliente null
        Prenotazione p1 = new Prenotazione(0, null, new Proiezione(1));
        boolean result1 = dao.create(p1);
        assertFalse(result1);

        // Caso 2: proiezione null
        Cliente cliente = new Cliente("a@b.com", "pwd", "Mario", "Rossi");
        Prenotazione p2 = new Prenotazione(0, cliente, null);
        boolean result2 = dao.create(p2);
        assertFalse(result2);
    }

    // -----------------------------------------------------------
    // Test del metodo retrieveById()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnPrenotazioneWhenFound(RepetitionInfo info) throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt("id")).thenReturn(5);
        when(mockResultSet.getString("email_cliente")).thenReturn("cliente@mail.com");
        when(mockResultSet.getInt("id_proiezione")).thenReturn(10);

        PrenotazioneDAO dao = new PrenotazioneDAO();
        Prenotazione result = dao.retrieveById(5);

        assertNotNull(result);
        assertEquals(5, result.getId());
        assertEquals("cliente@mail.com", result.getCliente().getEmail());
        assertEquals(10, result.getProiezione().getId());
        verify(mockPreparedStatement).setInt(1, 5);
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenPrenotazioneNotFound(RepetitionInfo info) throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        PrenotazioneDAO dao = new PrenotazioneDAO();
        Prenotazione result = dao.retrieveById(99);

        assertNull(result);
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenSQLExceptionInRetrieveById(RepetitionInfo info) throws Exception {
        when(mockDataSource.getConnection()).thenThrow(new SQLException("Errore DB"));

        PrenotazioneDAO dao = new PrenotazioneDAO();
        Prenotazione result = dao.retrieveById(1);

        assertNull(result);
    }

    // -----------------------------------------------------------
    // Test del metodo retrieveAllByCliente()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnPrenotazioniWhenFound(RepetitionInfo info) throws Exception {
        Cliente cliente = new Cliente("cliente@mail.com", "pwd", "Mario", "Rossi");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

        // Prima riga di risultato
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getInt("prenotazione_id")).thenReturn(1);
        when(mockResultSet.getInt("proiezione_id")).thenReturn(10);
        when(mockResultSet.getDate("data_proiezione")).thenReturn(Date.valueOf(LocalDate.now()));
        when(mockResultSet.getTime("ora_inizio")).thenReturn(Time.valueOf("20:30:00"));
        when(mockResultSet.getInt("film_id")).thenReturn(100);
        when(mockResultSet.getString("film_titolo")).thenReturn("Film Test");
        when(mockResultSet.getInt("durata")).thenReturn(120);
        when(mockResultSet.getInt("sala_id")).thenReturn(5);
        when(mockResultSet.getInt("numero_sala")).thenReturn(2);
        when(mockResultSet.getString("fila_posto")).thenReturn("A");
        when(mockResultSet.getInt("numero_posto")).thenReturn(1);

        // Mock delle new SedeDAO() e SalaDAO()
        Sede sede = new Sede(1, "Sede Test", "Via Roma");
        Sala sala = new Sala(5, 2, 100, sede);
        try (
                MockedConstruction<SedeDAO> mockedSedeDAO = mockConstruction(
                        SedeDAO.class,
                        (mock, context) -> when(mock.retrieveById(anyInt())).thenReturn(sede)
                );
                MockedConstruction<SalaDAO> mockedSalaDAO = mockConstruction(
                        SalaDAO.class,
                        (mock, context) -> when(mock.retrieveById(anyInt())).thenReturn(sala)
                )
        ) {
            PrenotazioneDAO dao = new PrenotazioneDAO();
            List<Prenotazione> result = dao.retrieveAllByCliente(cliente);

            assertNotNull(result);
            assertFalse(result.isEmpty());
            assertEquals(1, result.size());
            verify(mockPreparedStatement).setString(1, cliente.getEmail());
        }
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenSQLExceptionOccurs(RepetitionInfo info) throws Exception {
        Cliente cliente = new Cliente("cliente@mail.com", "pwd", "Mario", "Rossi");
        when(mockDataSource.getConnection()).thenThrow(new SQLException("Errore DB"));

        PrenotazioneDAO dao = new PrenotazioneDAO();
        List<Prenotazione> result = dao.retrieveAllByCliente(cliente);

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenNoResults(RepetitionInfo info) throws Exception {
        Cliente cliente = new Cliente("cliente@mail.com", "pwd", "Mario", "Rossi");
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        PrenotazioneDAO dao = new PrenotazioneDAO();
        List<Prenotazione> result = dao.retrieveAllByCliente(cliente);

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }
    @RepeatedTest(5)
    void shouldReturnNullWhenClienteIsNull() {
        PrenotazioneDAO dao = new PrenotazioneDAO();
        List<Prenotazione> result = dao.retrieveAllByCliente(null);
        assertNull(result);
    }
}
