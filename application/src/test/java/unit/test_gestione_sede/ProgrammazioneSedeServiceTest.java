package unit.test_gestione_sede;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.ProiezioneDAO;
import it.unisa.application.model.dao.SedeDAO;
import it.unisa.application.model.entity.*;
import it.unisa.application.sottosistemi.gestione_sede.service.ProgrammazioneSedeService;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.*;
import org.mockito.junit.jupiter.MockitoExtension;

import javax.sql.DataSource;
import java.lang.reflect.Field;
import java.sql.Connection;
import java.sql.Time;
import java.time.LocalDate;
import java.util.*;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test di unità per ProgrammazioneSedeService.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class ProgrammazioneSedeServiceTest {

    @Mock private ProiezioneDAO proiezioneDAO;
    @Mock private SedeDAO sedeDAO;

    @Mock private DataSource mockDataSource;
    @Mock private Connection mockConnection;

    private MockedStatic<DataSourceSingleton> mockedDataSourceSingleton;
    private ProgrammazioneSedeService service;

    @BeforeEach
    void setUp() throws Exception {
        // Mock statico per evitare connessioni DB reali
        mockedDataSourceSingleton = mockStatic(DataSourceSingleton.class);
        mockedDataSourceSingleton.when(DataSourceSingleton::getInstance).thenReturn(mockDataSource);
        lenient().when(mockDataSource.getConnection()).thenReturn(mockConnection);

        // Crea il service reale, poi sostituisci il DAO interno con il mock
        service = new ProgrammazioneSedeService();
        injectMock("proiezioneDAO", proiezioneDAO);
    }

    private void injectMock(String fieldName, Object mock) throws Exception {
        Field field = ProgrammazioneSedeService.class.getDeclaredField(fieldName);
        field.setAccessible(true);
        field.set(service, mock);
    }

    @AfterEach
    void tearDown() {
        mockedDataSourceSingleton.close();
    }

    // -----------------------------------------------------------
    // TEST: getProgrammazione()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnOnlyFutureProiezioniSortedByDateAndTime() {
        LocalDate today = LocalDate.now();
        Sede sede = new Sede(1, "Cinema Test", "Via Roma");
        Sala sala = new Sala(1, 1, 100, sede);
        Film film = new Film(1, "Film Test", "Azione", "PG", 120, new byte[1], "descrizione", false);

        Slot slot10 = new Slot(1, Time.valueOf("10:00:00"));
        Slot slot18 = new Slot(2, Time.valueOf("18:00:00"));

        Proiezione past = new Proiezione(1, sala, film, today.minusDays(1), slot10);
        Proiezione todayLate = new Proiezione(2, sala, film, today, slot18);
        Proiezione todayEarly = new Proiezione(3, sala, film, today, slot10);
        Proiezione future = new Proiezione(4, sala, film, today.plusDays(2), slot10);

        when(proiezioneDAO.retrieveAllBySede(1))
                .thenReturn(Arrays.asList(past, todayLate, todayEarly, future));

        List<Proiezione> result = service.getProgrammazione(1);

        assertNotNull(result);
        assertEquals(3, result.size());
        // Ordinate: oggi 10:00, oggi 18:00, futuro
        assertEquals(todayEarly.getId(), result.get(0).getId());
        assertEquals(todayLate.getId(), result.get(1).getId());
        assertEquals(future.getId(), result.get(2).getId());

        verify(proiezioneDAO).retrieveAllBySede(1);
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenNoProiezioni() {
        when(proiezioneDAO.retrieveAllBySede(anyInt())).thenReturn(Collections.emptyList());

        List<Proiezione> result = service.getProgrammazione(2);

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    // -----------------------------------------------------------
    // TEST: getProiezioniFilm()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnProiezioniWithinOneWeek() {
        LocalDate today = LocalDate.now();
        Sede sede = new Sede(1, "Sede A", "Via Roma");
        Sala sala = new Sala(1, 1, 100, sede);
        Film film = new Film(10, "Matrix", "Sci-Fi", "PG", 120, new byte[1], "desc", false);

        Proiezione past = new Proiezione(1, sala, film, today.minusDays(2), new Slot(1, Time.valueOf("09:00:00")));
        Proiezione withinWeek = new Proiezione(2, sala, film, today.plusDays(3), new Slot(2, Time.valueOf("11:00:00")));
        Proiezione beyondWeek = new Proiezione(3, sala, film, today.plusDays(10), new Slot(3, Time.valueOf("13:00:00")));

        when(proiezioneDAO.retrieveByFilm(any(Film.class), any(Sede.class)))
                .thenReturn(Arrays.asList(past, withinWeek, beyondWeek));

        List<Proiezione> result = service.getProiezioniFilm(10, 1);

        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals(withinWeek.getId(), result.getFirst().getId());
        verify(proiezioneDAO).retrieveByFilm(any(Film.class), any(Sede.class));
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenNoProiezioniForFilm() {
        when(proiezioneDAO.retrieveByFilm(any(Film.class), any(Sede.class)))
                .thenReturn(Collections.emptyList());

        List<Proiezione> result = service.getProiezioniFilm(1, 1);

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    // -----------------------------------------------------------
    // TEST: getCatalogoSede()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnCatalogoSedeSuccessfully() throws Exception {
        Sede sede = new Sede(1, "Cinema Test", "Via Roma");
        Film f1 = new Film(1, "Film1", "Azione", "PG", 100, new byte[1], "desc", false);
        Film f2 = new Film(2, "Film2", "Drammatico", "PG-13", 120, new byte[1], "desc", false);

        // Mock della creazione dinamica del SedeDAO interno
        try (MockedConstruction<SedeDAO> mockedSedeDAO = mockConstruction(SedeDAO.class,
                (mock, context) -> when(mock.retrieveFilm(1)).thenReturn(List.of(f1, f2)))) {

            List<Film> result = service.getCatalogoSede(sede);

            assertNotNull(result);
            assertEquals(2, result.size());
            assertEquals("Film1", result.getFirst().getTitolo());
            verify(mockedSedeDAO.constructed().getFirst()).retrieveFilm(1);
        }
    }

    @RepeatedTest(5)
    void shouldReturnEmptyCatalogoWhenSedeDAOReturnsEmpty() throws Exception {
        Sede sede = new Sede(1, "Cinema Test", "Via Roma");

        try (MockedConstruction<SedeDAO> mockedSedeDAO = mockConstruction(SedeDAO.class,
                (mock, context) -> when(mock.retrieveFilm(anyInt())).thenReturn(Collections.emptyList()))) {

            List<Film> result = service.getCatalogoSede(sede);

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }
    }
}
