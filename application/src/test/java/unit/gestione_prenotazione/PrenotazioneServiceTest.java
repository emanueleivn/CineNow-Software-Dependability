package unit.gestione_prenotazione;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.PostoProiezioneDAO;
import it.unisa.application.model.dao.PrenotazioneDAO;
import it.unisa.application.model.entity.*;
import it.unisa.application.sottosistemi.gestione_prenotazione.service.PrenotazioneService;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.*;
import org.mockito.junit.jupiter.MockitoExtension;

import javax.sql.DataSource;
import java.lang.reflect.Field;
import java.sql.Connection;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test di unità per PrenotazioneService.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class PrenotazioneServiceTest {

    @Mock private PrenotazioneDAO prenotazioneDAO;
    @Mock private PostoProiezioneDAO postoProiezioneDAO;

    @Mock private DataSource mockDataSource;
    @Mock private Connection mockConnection;

    private MockedStatic<DataSourceSingleton> mockedDataSourceSingleton;
    private PrenotazioneService service;

    private Cliente cliente;
    private Proiezione proiezione;
    private List<PostoProiezione> posti;

    @BeforeEach
    void setUp() throws Exception {
        // Mock statico DataSourceSingleton per bloccare la connessione reale
        mockedDataSourceSingleton = mockStatic(DataSourceSingleton.class);
        mockedDataSourceSingleton.when(DataSourceSingleton::getInstance).thenReturn(mockDataSource);
        lenient().when(mockDataSource.getConnection()).thenReturn(mockConnection);

        service = new PrenotazioneService();

        // Mock dao con reflection
        Field prenotazioneDAOField = PrenotazioneService.class.getDeclaredField("prenotazioneDAO");
        prenotazioneDAOField.setAccessible(true);
        prenotazioneDAOField.set(service, prenotazioneDAO);

        Field postoProiezioneDAOField = PrenotazioneService.class.getDeclaredField("postoProiezioneDAO");
        postoProiezioneDAOField.setAccessible(true);
        postoProiezioneDAOField.set(service, postoProiezioneDAO);

        cliente = new Cliente("mario@mail.com", "pwd", "Mario", "Rossi");
        proiezione = new Proiezione(1);
        posti = new ArrayList<>();
        Posto posto1 = new Posto(null, 'A', 1);
        Posto posto2 = new Posto(null, 'A', 2);
        posti.add(new PostoProiezione(posto1, proiezione));
        posti.add(new PostoProiezione(posto2, proiezione));
        posti.forEach(p -> p.setStato(true));
    }

    @AfterEach
    void tearDown() {
        mockedDataSourceSingleton.close();
    }

    // -----------------------------------------------------------
    // Test: aggiungiOrdine()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldCreatePrenotazioneAndOccupySeatsSuccessfully() {
        when(prenotazioneDAO.create(any(Prenotazione.class))).thenReturn(true);
        when(postoProiezioneDAO.occupaPosto(any(PostoProiezione.class), anyInt())).thenReturn(true);

        assertDoesNotThrow(() -> service.aggiungiOrdine(cliente, posti, proiezione));

        verify(prenotazioneDAO, times(1)).create(any(Prenotazione.class));
        verify(postoProiezioneDAO, times(2)).occupaPosto(any(PostoProiezione.class), anyInt());
    }

    @RepeatedTest(5)
    void shouldThrowRuntimeExceptionWhenPrenotazioneCreationFails() {
        when(prenotazioneDAO.create(any(Prenotazione.class))).thenReturn(false);

        assertThrows(RuntimeException.class,
                () -> service.aggiungiOrdine(cliente, posti, proiezione));

        verify(prenotazioneDAO).create(any(Prenotazione.class));
        verify(postoProiezioneDAO, never()).occupaPosto(any(), anyInt());
    }

    @RepeatedTest(5)
    void shouldThrowRuntimeExceptionWhenOccupazionePostoFails() {
        when(prenotazioneDAO.create(any(Prenotazione.class))).thenReturn(true);
        when(postoProiezioneDAO.occupaPosto(any(PostoProiezione.class), anyInt())).thenReturn(false);

        assertThrows(RuntimeException.class,
                () -> service.aggiungiOrdine(cliente, posti, proiezione));

        verify(prenotazioneDAO).create(any(Prenotazione.class));
        verify(postoProiezioneDAO).occupaPosto(any(PostoProiezione.class), anyInt());
    }

    @RepeatedTest(5)
    void shouldThrowIllegalArgumentWhenClienteIsNull() {
        assertThrows(IllegalArgumentException.class,
                () -> service.aggiungiOrdine(null, posti, proiezione));
        verifyNoInteractions(prenotazioneDAO, postoProiezioneDAO);
    }

    @RepeatedTest(5)
    void shouldThrowIllegalArgumentWhenPostiIsNull() {
        assertThrows(IllegalArgumentException.class,
                () -> service.aggiungiOrdine(cliente, null, proiezione));
        verifyNoInteractions(prenotazioneDAO, postoProiezioneDAO);
    }

    @RepeatedTest(5)
    void shouldThrowIllegalArgumentWhenPostiIsEmpty() {
        assertThrows(IllegalArgumentException.class,
                () -> service.aggiungiOrdine(cliente, new ArrayList<>(), proiezione));
        verifyNoInteractions(prenotazioneDAO, postoProiezioneDAO);
    }

    @RepeatedTest(5)
    void shouldThrowIllegalArgumentWhenProiezioneIsNull() {
        assertThrows(IllegalArgumentException.class,
                () -> service.aggiungiOrdine(cliente, posti, null));
        verifyNoInteractions(prenotazioneDAO, postoProiezioneDAO);
    }

    @RepeatedTest(5)
    void shouldThrowIllegalArgumentWhenPostoNotAvailable() {
        posti.getFirst().setStato(false);
        assertThrows(IllegalArgumentException.class,
                () -> service.aggiungiOrdine(cliente, posti, proiezione));
        verifyNoInteractions(prenotazioneDAO, postoProiezioneDAO);
    }

    // -----------------------------------------------------------
    // Test: ottieniPostiProiezione()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnListOfPostiProiezione() {
        Proiezione p = new Proiezione(10);
        List<PostoProiezione> expected = List.of(new PostoProiezione(new Posto(null, 'B', 3), p));
        when(postoProiezioneDAO.retrieveAllByProiezione(p)).thenReturn(expected);

        List<PostoProiezione> result = service.ottieniPostiProiezione(p);

        assertNotNull(result);
        assertEquals(1, result.size());
        verify(postoProiezioneDAO).retrieveAllByProiezione(p);
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenNoPostiFound() {
        Proiezione p = new Proiezione(15);
        when(postoProiezioneDAO.retrieveAllByProiezione(p)).thenReturn(new ArrayList<>());

        List<PostoProiezione> result = service.ottieniPostiProiezione(p);

        assertNotNull(result);
        assertTrue(result.isEmpty());
        verify(postoProiezioneDAO).retrieveAllByProiezione(p);
    }
}
