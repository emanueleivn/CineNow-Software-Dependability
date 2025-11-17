package unit.test_DAO;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.ProiezioneDAO;
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
 * Test di unità per ProiezioneDAO.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class ProiezioneDAOTest {

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
    void shouldCreateProiezioneSuccessfully() throws Exception {
        Film film = new Film(1, "Film Test", "Genere", "PG", 120, new byte[]{}, "desc", true);
        Sala sala = new Sala(2, 1, 100, new Sede(1));
        Slot slot = new Slot(10, Time.valueOf("20:00:00"));
        Proiezione proiezione = new Proiezione(0, sala, film, LocalDate.now(), slot);

        PreparedStatement mockSlotQuery = mock(PreparedStatement.class);
        ResultSet mockSlotRs = mock(ResultSet.class);
        PreparedStatement mockInsertProiezione = mock(PreparedStatement.class);
        ResultSet mockGeneratedKeys = mock(ResultSet.class);
        PreparedStatement mockInsertPosti = mock(PreparedStatement.class);

        // Simula gli slot disponibili
        when(mockConnection.prepareStatement(contains("SELECT id, ora_inizio"))).thenReturn(mockSlotQuery);
        when(mockSlotQuery.executeQuery()).thenReturn(mockSlotRs);
        when(mockSlotRs.next()).thenReturn(true, true, false);
        when(mockSlotRs.getInt("id")).thenReturn(10, 11);
        when(mockSlotRs.getTime("ora_inizio")).thenReturn(Time.valueOf("20:00:00"), Time.valueOf("22:00:00"));

        when(mockConnection.prepareStatement(startsWith("INSERT INTO proiezione"), eq(Statement.RETURN_GENERATED_KEYS)))
                .thenReturn(mockInsertProiezione);
        when(mockInsertProiezione.executeUpdate()).thenReturn(1);
        when(mockInsertProiezione.getGeneratedKeys()).thenReturn(mockGeneratedKeys);
        when(mockGeneratedKeys.next()).thenReturn(true);
        when(mockGeneratedKeys.getInt(1)).thenReturn(42);

        when(mockConnection.prepareStatement(startsWith("INSERT INTO posto_proiezione"))).thenReturn(mockInsertPosti);
        when(mockInsertPosti.executeUpdate()).thenReturn(1);

        ProiezioneDAO dao = new ProiezioneDAO();
        boolean result = dao.create(proiezione);

        assertTrue(result);
        assertEquals(42, proiezione.getId());
        verify(mockConnection).commit();
        verify(mockInsertProiezione).executeUpdate();
        verify(mockInsertPosti).executeUpdate();
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenSQLExceptionOccursInCreate() throws Exception {
        when(mockDataSource.getConnection()).thenThrow(new SQLException("Connessione fallita"));
        Film film = new Film(1, "Film", "", "", 120, new byte[]{}, "", true);
        Sala sala = new Sala(2, 1, 100, new Sede(1));
        Slot slot = new Slot(5, Time.valueOf("18:00:00"));
        Proiezione proiezione = new Proiezione(0, sala, film, LocalDate.now(), slot);

        ProiezioneDAO dao = new ProiezioneDAO();
        boolean result = dao.create(proiezione);

        assertFalse(result);
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenProiezioneIsNull() {
        ProiezioneDAO dao = new ProiezioneDAO();
        boolean success = dao.create(null);
        assertFalse(success, "Il metodo create() deve restituire false se la proiezione è null");
    }

    @RepeatedTest(5)
    void shouldThrowRuntimeExceptionWhenStartingSlotNotFoundInCreate() throws Exception {
        Film film = new Film(1, "Film Test", "Genere", "PG", 120, new byte[]{}, "desc", true);
        Sala sala = new Sala(2, 1, 100, new Sede(1));
        // slot con id che NON compare nella lista degli slot disponibili
        Slot startingSlot = new Slot(99, Time.valueOf("18:00:00"));
        Proiezione proiezione = new Proiezione(0, sala, film, LocalDate.now(), startingSlot);

        PreparedStatement mockSlotQuery = mock(PreparedStatement.class);
        ResultSet mockSlotRs = mock(ResultSet.class);

        when(mockConnection.prepareStatement(contains("SELECT id, ora_inizio"))).thenReturn(mockSlotQuery);
        when(mockSlotQuery.executeQuery()).thenReturn(mockSlotRs);
        when(mockSlotRs.next()).thenReturn(true, true, false);
        when(mockSlotRs.getInt("id")).thenReturn(1, 2);
        when(mockSlotRs.getTime("ora_inizio")).thenReturn(Time.valueOf("18:00:00"), Time.valueOf("20:00:00"));

        ProiezioneDAO dao = new ProiezioneDAO();

        RuntimeException ex = assertThrows(RuntimeException.class, () -> dao.create(proiezione));
        assertEquals("Slot di partenza non trovato.", ex.getMessage());
    }

    // SQLException durante l'insert -> catch + rollback eseguito
    @RepeatedTest(5)
    void shouldRollbackTransactionWhenSQLExceptionDuringCreate() throws Exception {
        Film film = new Film(1, "Film Test", "Genere", "PG", 120, new byte[]{}, "desc", true);
        Sala sala = new Sala(2, 1, 100, new Sede(1));
        Slot slot = new Slot(10, Time.valueOf("20:00:00"));
        Proiezione proiezione = new Proiezione(0, sala, film, LocalDate.now(), slot);

        PreparedStatement mockSlotQuery = mock(PreparedStatement.class);
        ResultSet mockSlotRs = mock(ResultSet.class);

        when(mockDataSource.getConnection()).thenReturn(mockConnection, mockConnection);

        when(mockConnection.prepareStatement(contains("SELECT id, ora_inizio"))).thenReturn(mockSlotQuery);
        when(mockSlotQuery.executeQuery()).thenReturn(mockSlotRs);
        when(mockSlotRs.next()).thenReturn(true, true, false);
        when(mockSlotRs.getInt("id")).thenReturn(10, 11);
        when(mockSlotRs.getTime("ora_inizio")).thenReturn(Time.valueOf("20:00:00"), Time.valueOf("22:00:00"));

        // L'eccezione avviene durante la preparazione dell'INSERT proiezione
        when(mockConnection.prepareStatement(startsWith("INSERT INTO proiezione"), eq(Statement.RETURN_GENERATED_KEYS)))
                .thenThrow(new SQLException("Insert error"));

        ProiezioneDAO dao = new ProiezioneDAO();
        boolean result = dao.create(proiezione);

        assertFalse(result);
        verify(mockConnection).setAutoCommit(false);
        // il rollback viene chiamato sul secondo getConnection, che in questo caso è lo stesso mock
        verify(mockConnection, times(1)).rollback();
    }

    // affectedRows == 0 (branch else di if (affectedRows > 0))
    @RepeatedTest(5)
    void shouldNotInsertPostiWhenInsertProiezioneAffectsNoRowsInCreate() throws Exception {
        Film film = new Film(1, "Film Test", "Genere", "PG", 120, new byte[]{}, "desc", true);
        Sala sala = new Sala(2, 1, 100, new Sede(1));
        Slot slot = new Slot(10, Time.valueOf("20:00:00"));
        Proiezione proiezione = new Proiezione(0, sala, film, LocalDate.now(), slot);

        PreparedStatement mockSlotQuery = mock(PreparedStatement.class);
        ResultSet mockSlotRs = mock(ResultSet.class);
        PreparedStatement mockInsertProiezione = mock(PreparedStatement.class);

        when(mockConnection.prepareStatement(contains("SELECT id, ora_inizio"))).thenReturn(mockSlotQuery);
        when(mockSlotQuery.executeQuery()).thenReturn(mockSlotRs);
        when(mockSlotRs.next()).thenReturn(true, true, false);
        // lo slot di partenza è presente
        when(mockSlotRs.getInt("id")).thenReturn(10, 11);
        when(mockSlotRs.getTime("ora_inizio")).thenReturn(Time.valueOf("20:00:00"), Time.valueOf("22:00:00"));

        when(mockConnection.prepareStatement(startsWith("INSERT INTO proiezione"), eq(Statement.RETURN_GENERATED_KEYS)))
                .thenReturn(mockInsertProiezione);
        when(mockInsertProiezione.executeUpdate()).thenReturn(0); // nessuna riga inserita

        ProiezioneDAO dao = new ProiezioneDAO();
        boolean result = dao.create(proiezione);

        assertTrue(result); // il metodo comunque fa commit e ritorna true
        verify(mockInsertProiezione).executeUpdate();
        assertEquals(0, proiezione.getId(), "L'ID non deve essere aggiornato se non ci sono righe inserite");
    }

    // branch else dell'if interno ramo False
    @RepeatedTest(5)
    void shouldHandleMissingGeneratedKeysInCreate() throws Exception {
        Film film = new Film(1, "Film Test", "Genere", "PG", 120, new byte[]{}, "desc", true);
        Sala sala = new Sala(2, 1, 100, new Sede(1));
        Slot slot = new Slot(10, Time.valueOf("20:00:00"));
        Proiezione proiezione = new Proiezione(0, sala, film, LocalDate.now(), slot);

        PreparedStatement mockSlotQuery = mock(PreparedStatement.class);
        ResultSet mockSlotRs = mock(ResultSet.class);
        PreparedStatement mockInsertProiezione = mock(PreparedStatement.class);
        ResultSet mockGeneratedKeys = mock(ResultSet.class);

        when(mockConnection.prepareStatement(contains("SELECT id, ora_inizio"))).thenReturn(mockSlotQuery);
        when(mockSlotQuery.executeQuery()).thenReturn(mockSlotRs);
        when(mockSlotRs.next()).thenReturn(true, true, false);
        when(mockSlotRs.getInt("id")).thenReturn(10, 11); // slot di partenza presente
        when(mockSlotRs.getTime("ora_inizio")).thenReturn(Time.valueOf("20:00:00"), Time.valueOf("22:00:00"));

        when(mockConnection.prepareStatement(startsWith("INSERT INTO proiezione"), eq(Statement.RETURN_GENERATED_KEYS)))
                .thenReturn(mockInsertProiezione);
        when(mockInsertProiezione.executeUpdate()).thenReturn(1);
        when(mockInsertProiezione.getGeneratedKeys()).thenReturn(mockGeneratedKeys);
        when(mockGeneratedKeys.next()).thenReturn(false); // nessuna chiave generata

        ProiezioneDAO dao = new ProiezioneDAO();
        boolean result = dao.create(proiezione);

        assertTrue(result);
        assertEquals(0, proiezione.getId(), "Se non ci sono chiavi generate, l'id rimane 0");
    }

    // -----------------------------------------------------------
    // Test del metodo retrieveById()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnProiezioneWhenFound() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt("id")).thenReturn(1);
        when(mockResultSet.getDate("data")).thenReturn(Date.valueOf(LocalDate.now()));
        when(mockResultSet.getInt("id_film")).thenReturn(5);
        when(mockResultSet.getInt("id_sala")).thenReturn(2);
        when(mockResultSet.getInt("id_orario")).thenReturn(3);

        ProiezioneDAO dao = new ProiezioneDAO();
        Proiezione result = dao.retrieveById(1);

        assertNotNull(result);
        assertEquals(1, result.getId());
        assertEquals(2, result.getSalaProiezione().getId());
        verify(mockPreparedStatement).setInt(1, 1);
    }

    // ramo else dell'if (rs.next()) in retrieveById
    @RepeatedTest(5)
    void shouldReturnNullWhenProiezioneNotFoundById() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        ProiezioneDAO dao = new ProiezioneDAO();
        Proiezione result = dao.retrieveById(999);

        assertNull(result);
        verify(mockPreparedStatement).setInt(1, 999);
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenSQLExceptionOccursInRetrieveById() throws Exception {
        when(mockDataSource.getConnection()).thenThrow(new SQLException("Errore DB"));

        ProiezioneDAO dao = new ProiezioneDAO();
        Proiezione result = dao.retrieveById(1);

        assertNull(result);
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenParametersAreNull() {
        ProiezioneDAO dao = new ProiezioneDAO();
        List<Proiezione> p = dao.retrieveByFilm(null,null);
        assertNull(p, "Il metodo retriveByFilm() deve restituire false se film e sede sono null");
        Film film = new Film(1, "Film", "", "", 120, new byte[]{}, "", true);
        Sede sede = new Sede(1, "Sede", "Indirizzo");
        p = dao.retrieveByFilm(film, null);
        assertNull(p, "Il metodo retriveByFilm() deve restituire false se sede è null");
        p = dao.retrieveByFilm(null, sede);
        assertNull(p, "Il metodo retriveByFilm() deve restituire false se film è null");
    }
    // -----------------------------------------------------------
    // Test del metodo retrieveByFilm()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnProiezioniForGivenFilmAndSede() throws Exception {
        Film film = new Film(1, "Film A", "", "", 120, new byte[]{}, "", true);
        Sede sede = new Sede(1, "Sede Test", "Via Roma");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getInt("id")).thenReturn(10);
        when(mockResultSet.getDate("data")).thenReturn(Date.valueOf(LocalDate.now()));
        when(mockResultSet.getInt("id_sala")).thenReturn(5);
        when(mockResultSet.getInt("numero_sala")).thenReturn(2);
        when(mockResultSet.getInt("id_film")).thenReturn(1);
        when(mockResultSet.getString("titolo_film")).thenReturn("Film A");
        when(mockResultSet.getInt("durata_film")).thenReturn(120);
        when(mockResultSet.getInt("id_orario")).thenReturn(3);
        when(mockResultSet.getTime("orario")).thenReturn(Time.valueOf("18:00:00"));

        ProiezioneDAO dao = new ProiezioneDAO();
        List<Proiezione> result = dao.retrieveByFilm(film, sede);

        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals("Film A", result.getFirst().getFilmProiezione().getTitolo());
        verify(mockPreparedStatement).setInt(1, film.getId());
        verify(mockPreparedStatement).setInt(2, sede.getId());
    }

    // Due proiezioni con stesso film/sala/data ma NON sovrapposte
    @RepeatedTest(5)
    void shouldAllowNonOverlappingProiezioniInRetrieveByFilm() throws Exception {
        Film film = new Film(1, "Film A", "", "", 120, new byte[]{}, "", true);
        Sede sede = new Sede(1, "Sede Test", "Via Roma");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

        when(mockResultSet.next()).thenReturn(true, true, false);

        LocalDate today = LocalDate.now();
        when(mockResultSet.getInt("id")).thenReturn(10, 11);
        when(mockResultSet.getDate("data")).thenReturn(Date.valueOf(today), Date.valueOf(today));
        when(mockResultSet.getInt("id_sala")).thenReturn(5, 5);
        when(mockResultSet.getInt("numero_sala")).thenReturn(2, 2);
        when(mockResultSet.getInt("id_film")).thenReturn(1, 1);
        when(mockResultSet.getString("titolo_film")).thenReturn("Film A", "Film A");
        when(mockResultSet.getInt("durata_film")).thenReturn(120, 120);
        when(mockResultSet.getInt("id_orario")).thenReturn(3, 4);
        // prima proiezione 18:00, seconda 21:00 -> nessuna sovrapposizione
        when(mockResultSet.getTime("orario")).thenReturn(
                Time.valueOf("18:00:00"),
                Time.valueOf("21:00:00")
        );

        ProiezioneDAO dao = new ProiezioneDAO();
        List<Proiezione> result = dao.retrieveByFilm(film, sede);

        assertNotNull(result);
        assertEquals(2, result.size(), "Le proiezioni non sovrapposte devono essere entrambe mantenute");
    }

    //due proiezioni sovrapposte -> la seconda deve essere scartata
    @RepeatedTest(5)
    void shouldFilterOverlappingProiezioniInRetrieveByFilm() throws Exception {
        Film film = new Film(1, "Film A", "", "", 120, new byte[]{}, "", true);
        Sede sede = new Sede(1, "Sede Test", "Via Roma");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

        when(mockResultSet.next()).thenReturn(true, true, false);

        LocalDate today = LocalDate.now();
        when(mockResultSet.getInt("id")).thenReturn(10, 11);
        when(mockResultSet.getDate("data")).thenReturn(Date.valueOf(today), Date.valueOf(today));
        when(mockResultSet.getInt("id_sala")).thenReturn(5, 5);
        when(mockResultSet.getInt("numero_sala")).thenReturn(2, 2);
        when(mockResultSet.getInt("id_film")).thenReturn(1, 1);
        when(mockResultSet.getString("titolo_film")).thenReturn("Film A", "Film A");
        when(mockResultSet.getInt("durata_film")).thenReturn(120, 120);
        when(mockResultSet.getInt("id_orario")).thenReturn(3, 4);
        when(mockResultSet.getTime("orario")).thenReturn(
                Time.valueOf("18:00:00"),
                Time.valueOf("19:00:00")
        );

        ProiezioneDAO dao = new ProiezioneDAO();
        List<Proiezione> result = dao.retrieveByFilm(film, sede);

        assertNotNull(result);
        assertEquals(1, result.size(), "La seconda proiezione sovrapposta non deve essere aggiunta");
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenSQLExceptionInRetrieveByFilm(RepetitionInfo info) throws Exception {
        Film film = new Film(1, "Film A", "", "", 120, new byte[]{}, "", true);
        Sede sede = new Sede(1);

        when(mockDataSource.getConnection()).thenThrow(new SQLException("Connessione fallita"));

        ProiezioneDAO dao = new ProiezioneDAO();
        List<Proiezione> result = dao.retrieveByFilm(film, sede);

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    // -----------------------------------------------------------
    // Test del metodo retrieveAllBySede()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnProiezioniForGivenSede() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getInt("id")).thenReturn(10);
        when(mockResultSet.getDate("data")).thenReturn(Date.valueOf(LocalDate.now()));
        when(mockResultSet.getInt("id_sala")).thenReturn(5);
        when(mockResultSet.getInt("numero_sala")).thenReturn(2);
        when(mockResultSet.getInt("id_film")).thenReturn(3);
        when(mockResultSet.getString("titolo_film")).thenReturn("Film B");
        when(mockResultSet.getInt("durata_film")).thenReturn(90);
        when(mockResultSet.getInt("id_orario")).thenReturn(7);
        when(mockResultSet.getTime("orario")).thenReturn(Time.valueOf("20:00:00"));

        ProiezioneDAO dao = new ProiezioneDAO();
        List<Proiezione> result = dao.retrieveAllBySede(1);

        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals("Film B", result.getFirst().getFilmProiezione().getTitolo());
        verify(mockPreparedStatement).setInt(1, 1);
    }

    //due proiezioni non sovrapposte in retrieveAllBySede (branch FALSE)
    @RepeatedTest(5)
    void shouldAllowNonOverlappingProiezioniInRetrieveAllBySede() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

        when(mockResultSet.next()).thenReturn(true, true, false);

        LocalDate today = LocalDate.now();
        when(mockResultSet.getInt("id")).thenReturn(10, 11);
        when(mockResultSet.getDate("data")).thenReturn(Date.valueOf(today), Date.valueOf(today));
        when(mockResultSet.getInt("id_sala")).thenReturn(5, 5);
        when(mockResultSet.getInt("numero_sala")).thenReturn(2, 2);
        when(mockResultSet.getInt("id_film")).thenReturn(3, 3);
        when(mockResultSet.getString("titolo_film")).thenReturn("Film B", "Film B");
        when(mockResultSet.getInt("durata_film")).thenReturn(90, 90);
        when(mockResultSet.getInt("id_orario")).thenReturn(7, 8);
        when(mockResultSet.getTime("orario")).thenReturn(
                Time.valueOf("20:00:00"),
                Time.valueOf("22:00:00")
        );

        ProiezioneDAO dao = new ProiezioneDAO();
        List<Proiezione> result = dao.retrieveAllBySede(1);

        assertNotNull(result);
        assertEquals(2, result.size(), "Proiezioni non sovrapposte devono essere mantenute");
    }

    // due proiezioni sovrapposte in retrieveAllBySede (branch TRUE)
    @RepeatedTest(5)
    void shouldFilterOverlappingProiezioniInRetrieveAllBySede() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

        when(mockResultSet.next()).thenReturn(true, true, false);

        LocalDate today = LocalDate.now();
        when(mockResultSet.getInt("id")).thenReturn(10, 11);
        when(mockResultSet.getDate("data")).thenReturn(Date.valueOf(today), Date.valueOf(today));
        when(mockResultSet.getInt("id_sala")).thenReturn(5, 5);
        when(mockResultSet.getInt("numero_sala")).thenReturn(2, 2);
        when(mockResultSet.getInt("id_film")).thenReturn(3, 3);
        when(mockResultSet.getString("titolo_film")).thenReturn("Film B", "Film B");
        when(mockResultSet.getInt("durata_film")).thenReturn(90, 90);
        when(mockResultSet.getInt("id_orario")).thenReturn(7, 8);
        when(mockResultSet.getTime("orario")).thenReturn(
                Time.valueOf("20:00:00"),
                Time.valueOf("21:00:00")
        );

        ProiezioneDAO dao = new ProiezioneDAO();
        List<Proiezione> result = dao.retrieveAllBySede(1);

        assertNotNull(result);
        assertEquals(1, result.size(), "La seconda proiezione sovrapposta non deve essere aggiunta");
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenSQLExceptionInRetrieveAllBySede() throws Exception {
        when(mockDataSource.getConnection()).thenThrow(new SQLException("Errore DB"));

        ProiezioneDAO dao = new ProiezioneDAO();
        List<Proiezione> result = dao.retrieveAllBySede(1);

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    // -----------------------------------------------------------
    // Test del metodo retrieveProiezioneBySalaSlotAndData()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnProiezioneBySalaSlotAndData() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt("id")).thenReturn(1);
        when(mockResultSet.getDate("data")).thenReturn(Date.valueOf(LocalDate.now()));
        when(mockResultSet.getInt("id_film")).thenReturn(2);
        when(mockResultSet.getInt("id_sala")).thenReturn(5);
        when(mockResultSet.getInt("id_orario")).thenReturn(10);

        ProiezioneDAO dao = new ProiezioneDAO();
        Proiezione result = dao.retrieveProiezioneBySalaSlotAndData(5, 10, LocalDate.now());

        assertNotNull(result);
        assertEquals(1, result.getId());
        assertEquals(5, result.getSalaProiezione().getId());
        verify(mockPreparedStatement).setInt(1, 5);
        verify(mockPreparedStatement).setInt(2, 10);
    }

    @RepeatedTest(5)
    void shouldReturnNullWhenSQLExceptionInRetrieveProiezioneBySalaSlotAndData() throws Exception {
        when(mockDataSource.getConnection()).thenThrow(new SQLException("Connessione fallita"));

        ProiezioneDAO dao = new ProiezioneDAO();
        Proiezione result = dao.retrieveProiezioneBySalaSlotAndData(5, 10, LocalDate.now());

        assertNull(result);
    }

    //ramo else dell'if (rs.next()) in retrieveProiezioneBySalaSlotAndData
    @RepeatedTest(5)
    void shouldReturnNullWhenNoProiezioneFoundBySalaSlotAndData() throws Exception {
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        ProiezioneDAO dao = new ProiezioneDAO();
        Proiezione result = dao.retrieveProiezioneBySalaSlotAndData(5, 10, LocalDate.now());

        assertNull(result);
    }
}
