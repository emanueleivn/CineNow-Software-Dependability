package unit.gestione_prenotazione;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.PrenotazioneDAO;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.model.entity.Prenotazione;
import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.sottosistemi.gestione_prenotazione.service.StoricoOrdiniService;
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
 * Test di unità per StoricoOrdiniService
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class StoricoOrdiniServiceTest {

    @Mock
    private PrenotazioneDAO prenotazioneDAO;

    @Mock
    private DataSource mockDataSource;
    @Mock
    private Connection mockConnection;

    private MockedStatic<DataSourceSingleton> mockedDataSourceSingleton;
    private StoricoOrdiniService service;
    private Cliente cliente;

    @BeforeEach
    void setUp() throws Exception {
        // Mock dello statico DataSourceSingleton per bloccare la connessione reale
        mockedDataSourceSingleton = mockStatic(DataSourceSingleton.class);
        mockedDataSourceSingleton.when(DataSourceSingleton::getInstance).thenReturn(mockDataSource);
        lenient().when(mockDataSource.getConnection()).thenReturn(mockConnection);

        service = new StoricoOrdiniService();

       // Sostituzione del DAO interno con il mock tramite reflection
        Field daoField = StoricoOrdiniService.class.getDeclaredField("prenotazioneDAO");
        daoField.setAccessible(true);
        daoField.set(service, prenotazioneDAO);

        cliente = new Cliente("cliente@mail.com", "pwd", "Mario", "Rossi");
    }

    @AfterEach
    void tearDown() {
        mockedDataSourceSingleton.close();
    }

    // -----------------------------------------------------------
    // Test: storicoOrdini()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnListOfPrenotazioniWhenFound() {
        List<Prenotazione> expectedList = new ArrayList<>();
        expectedList.add(new Prenotazione(1, cliente, new Proiezione(10)));
        expectedList.add(new Prenotazione(2, cliente, new Proiezione(11)));

        when(prenotazioneDAO.retrieveAllByCliente(cliente)).thenReturn(expectedList);

        List<Prenotazione> result = service.storicoOrdini(cliente);

        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals(1, result.get(0).getId());
        assertEquals(2, result.get(1).getId());
        verify(prenotazioneDAO, times(1)).retrieveAllByCliente(cliente);
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenNoPrenotazioniFound() {
        when(prenotazioneDAO.retrieveAllByCliente(cliente)).thenReturn(new ArrayList<>());

        List<Prenotazione> result = service.storicoOrdini(cliente);

        assertNotNull(result);
        assertTrue(result.isEmpty());
        verify(prenotazioneDAO).retrieveAllByCliente(cliente);
    }

    @RepeatedTest(5)
    void shouldThrowIllegalArgumentExceptionWhenClienteIsNull() {
        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class,
                () -> service.storicoOrdini(null));

        assertEquals("Il cliente non può essere null.", ex.getMessage());
        verifyNoInteractions(prenotazioneDAO);
    }

    @RepeatedTest(5)
    void shouldPropagateRuntimeExceptionFromDAO() {
        when(prenotazioneDAO.retrieveAllByCliente(cliente))
                .thenThrow(new RuntimeException("Errore DAO"));

        RuntimeException ex = assertThrows(RuntimeException.class,
                () -> service.storicoOrdini(cliente));

        assertEquals("Errore DAO", ex.getMessage());
        verify(prenotazioneDAO).retrieveAllByCliente(cliente);
    }
}
