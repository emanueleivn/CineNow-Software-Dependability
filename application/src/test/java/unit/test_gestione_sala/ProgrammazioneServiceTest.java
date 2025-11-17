package unit.test_gestione_sala;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.*;
import it.unisa.application.model.entity.*;
import it.unisa.application.sottosistemi.gestione_sala.service.ProgrammazioneService;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.*;
import org.mockito.junit.jupiter.MockitoExtension;

import javax.sql.DataSource;
import java.lang.reflect.Field;
import java.sql.Connection;
import java.sql.Time;
import java.time.LocalDate;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test di unità per ProgrammazioneService.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class ProgrammazioneServiceTest {

    @Mock private FilmDAO filmDAO;
    @Mock private SalaDAO salaDAO;
    @Mock private SlotDAO slotDAO;
    @Mock private ProiezioneDAO proiezioneDAO;

    @Mock private DataSource mockDataSource;
    @Mock private Connection mockConnection;

    private MockedStatic<DataSourceSingleton> mockedDataSourceSingleton;
    private ProgrammazioneService service;

    @BeforeEach
    void setUp() throws Exception {
        // Mock dello statico DataSourceSingleton per evitare connessioni reali
        mockedDataSourceSingleton = mockStatic(DataSourceSingleton.class);
        mockedDataSourceSingleton.when(DataSourceSingleton::getInstance).thenReturn(mockDataSource);
        lenient().when(mockDataSource.getConnection()).thenReturn(mockConnection);

        service = new ProgrammazioneService();

        // Iniezione dei mock tramite reflection
        injectMock("filmDAO", filmDAO);
        injectMock("salaDAO", salaDAO);
        injectMock("slotDAO", slotDAO);
        injectMock("proiezioneDAO", proiezioneDAO);
    }

    private void injectMock(String fieldName, Object mock) throws Exception {
        Field field = ProgrammazioneService.class.getDeclaredField(fieldName);
        field.setAccessible(true);
        field.set(service, mock);
    }

    @AfterEach
    void tearDown() {
        mockedDataSourceSingleton.close();
    }

    // -----------------------------------------------------------
    // Test: aggiungiProiezione()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldAddProiezioneSuccessfully() {
        Film film = new Film(1, "Film Test", "Azione", "PG", 120, new byte[1], "desc", false);
        Sala sala = new Sala(2, 1, 100, null);
        List<Slot> allSlots = Arrays.asList(
                new Slot(1, Time.valueOf("15:00:00")),
                new Slot(2, Time.valueOf("18:00:00"))
        );
        List<Integer> slotIds = List.of(2);

        when(filmDAO.retrieveById(1)).thenReturn(film);
        when(salaDAO.retrieveById(2)).thenReturn(sala);
        when(slotDAO.retrieveAllSlots()).thenReturn(allSlots);
        when(proiezioneDAO.create(any(Proiezione.class))).thenReturn(true);

        boolean result = service.aggiungiProiezione(1, 2, slotIds, LocalDate.now().plusDays(1));

        assertTrue(result);
        verify(filmDAO).retrieveById(1);
        verify(salaDAO).retrieveById(2);
        verify(slotDAO).retrieveAllSlots();
        verify(proiezioneDAO).create(any(Proiezione.class));
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenFilmNotFound() {
        when(filmDAO.retrieveById(1)).thenReturn(null);

        boolean result = service.aggiungiProiezione(1, 2, List.of(1), LocalDate.now().plusDays(1));

        assertFalse(result);
        verify(filmDAO).retrieveById(1);
        verifyNoInteractions(proiezioneDAO);
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenSalaNotFound() {
        Film film = new Film(1, "Film Test", "Azione", "PG", 120, new byte[1], "desc", false);
        when(filmDAO.retrieveById(1)).thenReturn(film);
        when(salaDAO.retrieveById(2)).thenReturn(null);

        boolean result = service.aggiungiProiezione(1, 2, List.of(1), LocalDate.now().plusDays(1));

        assertFalse(result);
        verify(salaDAO).retrieveById(2);
        verify(proiezioneDAO, never()).create(any());
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenDateIsPast() {
        Film film = new Film(1, "Film Test", "Azione", "PG", 120, new byte[1], "desc", false);
        Sala sala = new Sala(2, 1, 100, null);
        when(filmDAO.retrieveById(1)).thenReturn(film);
        when(salaDAO.retrieveById(2)).thenReturn(sala);

        boolean result = service.aggiungiProiezione(1, 2, List.of(1), LocalDate.now().minusDays(1));

        assertFalse(result);
        verify(proiezioneDAO, never()).create(any());
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenNoValidSlotSelected() {
        Film film = new Film(1, "Film Test", "Azione", "PG", 120, new byte[1], "desc", false);
        Sala sala = new Sala(2, 1, 100, null);
        List<Slot> allSlots = List.of(new Slot(5, Time.valueOf("10:00:00")));

        when(filmDAO.retrieveById(1)).thenReturn(film);
        when(salaDAO.retrieveById(2)).thenReturn(sala);
        when(slotDAO.retrieveAllSlots()).thenReturn(allSlots);

        boolean result = service.aggiungiProiezione(1, 2, List.of(1), LocalDate.now().plusDays(2));

        assertFalse(result);
        verify(slotDAO).retrieveAllSlots();
        verify(proiezioneDAO, never()).create(any());
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenCreateProiezioneFails() {
        Film film = new Film(1, "Film Test", "Azione", "PG", 120, new byte[1], "desc", false);
        Sala sala = new Sala(2, 1, 100, null);
        List<Slot> allSlots = List.of(new Slot(1, Time.valueOf("15:00:00")));

        when(filmDAO.retrieveById(1)).thenReturn(film);
        when(salaDAO.retrieveById(2)).thenReturn(sala);
        when(slotDAO.retrieveAllSlots()).thenReturn(allSlots);
        when(proiezioneDAO.create(any(Proiezione.class))).thenReturn(false);

        boolean result = service.aggiungiProiezione(1, 2, List.of(1), LocalDate.now().plusDays(1));

        assertFalse(result);
        verify(proiezioneDAO).create(any(Proiezione.class));
    }

    @RepeatedTest(5)
    void shouldReturnFalseWhenExceptionThrown() {
        when(filmDAO.retrieveById(anyInt())).thenThrow(new RuntimeException("Errore DB"));

        boolean result = service.aggiungiProiezione(1, 2, List.of(1), LocalDate.now().plusDays(1));

        assertFalse(result);
    }

    @RepeatedTest(5)
    void shouldSortSlotsWhenUnsorted() {
        Film film = new Film(1, "Film Test", "Azione", "PG", 120, new byte[1], "desc", false);
        Sala sala = new Sala(2, 1, 100, null);

        // Slot NON ordinati -> farà scattare il while
        Slot slotLate = new Slot(1, Time.valueOf("18:00:00"));
        Slot slotEarly = new Slot(2, Time.valueOf("10:00:00"));

        List<Slot> allSlots = Arrays.asList(slotLate, slotEarly);
        List<Integer> slotIds = List.of(1, 2); // seleziono entrambi

        when(filmDAO.retrieveById(1)).thenReturn(film);
        when(salaDAO.retrieveById(2)).thenReturn(sala);
        when(slotDAO.retrieveAllSlots()).thenReturn(allSlots);
        when(proiezioneDAO.create(any(Proiezione.class))).thenReturn(true);

        boolean result = service.aggiungiProiezione(1, 2, slotIds, LocalDate.now().plusDays(1));

        assertTrue(result);

        // Catturiamo la proiezione creata per verificare quale slot è stato usato
        ArgumentCaptor<Proiezione> captor = ArgumentCaptor.forClass(Proiezione.class);
        verify(proiezioneDAO).create(captor.capture());

        Proiezione created = captor.getValue();
        assertEquals(Time.valueOf("10:00:00"),
                created.getOrarioProiezione().getOraInizio(),
                "Lo slot più presto (10:00) deve essere scelto dopo l'ordinamento");
    }

}
