package unit.test_gestione_sala;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.FilmDAO;
import it.unisa.application.model.dao.ProiezioneDAO;
import it.unisa.application.model.dao.SlotDAO;
import it.unisa.application.model.entity.Film;
import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.model.entity.Slot;
import it.unisa.application.sottosistemi.gestione_sala.service.SlotService;
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
 * Test di unità per SlotService.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class SlotServiceTest {

    @Mock private SlotDAO slotDAO;
    @Mock private ProiezioneDAO proiezioneDAO;
    @Mock private FilmDAO filmDAO;

    @Mock private DataSource mockDataSource;
    @Mock private Connection mockConnection;

    private MockedStatic<DataSourceSingleton> mockedDataSourceSingleton;
    private SlotService service;

    @BeforeEach
    void setUp() throws Exception {
        // Mock statico per evitare connessioni reali
        mockedDataSourceSingleton = mockStatic(DataSourceSingleton.class);
        mockedDataSourceSingleton.when(DataSourceSingleton::getInstance).thenReturn(mockDataSource);
        lenient().when(mockDataSource.getConnection()).thenReturn(mockConnection);

        // Creazione del service e sostituzione dei DAO tramite reflection
        service = new SlotService();
        injectMock("slotDAO", slotDAO);
        injectMock("proiezioneDAO", proiezioneDAO);
        injectMock("filmDAO", filmDAO);
    }

    private void injectMock(String fieldName, Object mock) throws Exception {
        Field field = SlotService.class.getDeclaredField(fieldName);
        field.setAccessible(true);
        field.set(service, mock);
    }

    @AfterEach
    void tearDown() {
        mockedDataSourceSingleton.close();
    }

    // -----------------------------------------------------------
    // TEST slotDisponibili()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnCorrectCalendarWithAvailableAndOccupiedSlots() throws Exception {
        LocalDate start = LocalDate.now();
        LocalDate end = start.plusDays(1);

        // Film principale richiesto
        Film filmRichiesto = new Film(1, "Film Principale", "Azione", "PG", 120, new byte[1], "desc", false);
        when(filmDAO.retrieveById(1)).thenReturn(filmRichiesto);

        // Slot disponibili
        List<Slot> allSlots = Arrays.asList(
                new Slot(1, Time.valueOf("10:00:00")),
                new Slot(2, Time.valueOf("12:00:00")),
                new Slot(3, Time.valueOf("15:00:00"))
        );
        when(slotDAO.retrieveAllSlots()).thenReturn(allSlots);

        // Proiezione esistente solo per slot 2 nel primo giorno
        Film filmOccupante = new Film(5, "Film Occupato", "Commedia", "PG-13", 100, new byte[1], "desc", false);
        Proiezione proiezioneOccupata = new Proiezione(99, null, filmOccupante, start, allSlots.get(1));

        when(proiezioneDAO.retrieveProiezioneBySalaSlotAndData(eq(10), eq(2), eq(start)))
                .thenReturn(proiezioneOccupata);
        when(filmDAO.retrieveById(5)).thenReturn(filmOccupante);

        // Nessuna proiezione negli altri slot/giorni
        when(proiezioneDAO.retrieveProiezioneBySalaSlotAndData(anyInt(), anyInt(), eq(end)))
                .thenReturn(null);
        when(proiezioneDAO.retrieveProiezioneBySalaSlotAndData(eq(10), eq(1), eq(start)))
                .thenReturn(null);
        when(proiezioneDAO.retrieveProiezioneBySalaSlotAndData(eq(10), eq(3), eq(start)))
                .thenReturn(null);


        Map<String, Object> result = service.slotDisponibili(1, 10, start, end);


        assertNotNull(result);
        assertTrue(result.containsKey("durataFilm"));
        assertEquals(120, result.get("durataFilm"));

        List<Map<String, Object>> calendar = (List<Map<String, Object>>) result.get("calendar");
        assertEquals(2, calendar.size()); // due giorni nel range

        // ✅ Primo giorno: slot 2 occupato
        List<Map<String, Object>> slotsGiorno1 = (List<Map<String, Object>>) calendar.get(0).get("slots");
        Map<String, Object> slot2 = slotsGiorno1.stream()
                .filter(s -> (int) s.get("id") == 2)
                .findFirst().orElseThrow();
        assertTrue((boolean) slot2.get("occupato"));
        assertEquals("Film Occupato", slot2.get("film"));

        // ✅ Secondo giorno: tutti liberi
        List<Map<String, Object>> slotsGiorno2 = (List<Map<String, Object>>) calendar.get(1).get("slots");
        assertTrue(slotsGiorno2.stream().noneMatch(s -> (boolean) s.get("occupato")));

        verify(slotDAO, atLeastOnce()).retrieveAllSlots();
        verify(filmDAO, times(2)).retrieveById(anyInt());
    }

    @RepeatedTest(5)
    void shouldThrowExceptionWhenFilmNotFound() throws Exception {
        when(filmDAO.retrieveById(999)).thenReturn(null);

        assertThrows(RuntimeException.class,
                () -> service.slotDisponibili(999, 1, LocalDate.now(), LocalDate.now().plusDays(1)));
    }

    @RepeatedTest(5)
    void shouldReturnCalendarWithNoOccupiedSlots() throws Exception {
        LocalDate day = LocalDate.now();

        Film film = new Film(1, "Film Test", "Azione", "PG", 100, new byte[1], "desc", false);
        when(filmDAO.retrieveById(1)).thenReturn(film);

        List<Slot> allSlots = Arrays.asList(
                new Slot(1, Time.valueOf("09:00:00")),
                new Slot(2, Time.valueOf("11:00:00"))
        );
        when(slotDAO.retrieveAllSlots()).thenReturn(allSlots);
        when(proiezioneDAO.retrieveProiezioneBySalaSlotAndData(anyInt(), anyInt(), any(LocalDate.class)))
                .thenReturn(null);

        Map<String, Object> result = service.slotDisponibili(1, 10, day, day);

        assertNotNull(result);
        assertTrue(result.containsKey("calendar"));
        List<Map<String, Object>> calendar = (List<Map<String, Object>>) result.get("calendar");
        assertEquals(1, calendar.size());
        List<Map<String, Object>> slots = (List<Map<String, Object>>) calendar.get(0).get("slots");
        assertTrue(slots.stream().noneMatch(s -> (boolean) s.get("occupato")));
    }

    //Ramo FALSE dell'if su durata film > ultimo slot + 120 min
    @RepeatedTest(5)
    void shouldNotAddExtraSlotWhenFilmDurationIsShort() throws Exception {
        LocalDate day = LocalDate.now();

        Film film = new Film(1, "Film Corto", "Azione", "PG", 20, new byte[1], "desc", false);
        when(filmDAO.retrieveById(1)).thenReturn(film);

        // Ultimo slot della giornata
        Slot lastSlot = new Slot(1, Time.valueOf("10:00:00"));
        when(slotDAO.retrieveAllSlots()).thenReturn(List.of(lastSlot));

        // Nessuna proiezione esistente
        when(proiezioneDAO.retrieveProiezioneBySalaSlotAndData(anyInt(), eq(1), any(LocalDate.class)))
                .thenReturn(null);

        Map<String, Object> result = service.slotDisponibili(1, 10, day, day);

        assertNotNull(result);

        List<Map<String, Object>> calendar = (List<Map<String, Object>>) result.get("calendar");
        assertEquals(1, calendar.size());

        List<Map<String, Object>> slots = (List<Map<String, Object>>) calendar.get(0).get("slots");

        assertEquals(1, slots.size(), "Non deve essere aggiunto uno slot extra se la durata è <= 30 minuti");
    }


    @RepeatedTest(5)
    void shouldReturnFalseWhenExceptionOccurs() throws Exception {
        when(filmDAO.retrieveById(anyInt())).thenThrow(new RuntimeException("DB error"));

        assertThrows(RuntimeException.class, () ->
                service.slotDisponibili(1, 1, LocalDate.now(), LocalDate.now()));
    }
}
