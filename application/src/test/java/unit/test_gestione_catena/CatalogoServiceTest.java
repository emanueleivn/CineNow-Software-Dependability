package unit.test_gestione_catena;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.FilmDAO;
import it.unisa.application.model.entity.Film;
import it.unisa.application.sottosistemi.gestione_catena.service.CatalogoService;
import it.unisa.application.utilities.CampoValidator;
import it.unisa.application.utilities.ValidateStrategyManager;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.*;
import org.mockito.junit.jupiter.MockitoExtension;

import javax.sql.DataSource;
import java.lang.reflect.Field;
import java.sql.Connection;
import java.util.*;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test di unità per CatalogoService.
 */
@ExtendWith(MockitoExtension.class)
@TestInstance(TestInstance.Lifecycle.PER_METHOD)
class CatalogoServiceTest {

    @Mock
    private FilmDAO filmDAO;
    @Mock
    private ValidateStrategyManager validationManager;
    @Mock
    private DataSource mockDataSource;
    @Mock
    private Connection mockConnection;

    private MockedStatic<DataSourceSingleton> mockedDataSourceSingleton;
    private CatalogoService service;

    private byte[] locandinaValida;

    @BeforeEach
    void setUp() throws Exception {
        mockedDataSourceSingleton = mockStatic(DataSourceSingleton.class);
        mockedDataSourceSingleton.when(DataSourceSingleton::getInstance).thenReturn(mockDataSource);
        lenient().when(mockDataSource.getConnection()).thenReturn(mockConnection);

        // Istanziazione e sostituzione via reflection
        service = new CatalogoService();

        Field filmDAOField = CatalogoService.class.getDeclaredField("filmDAO");
        filmDAOField.setAccessible(true);
        filmDAOField.set(service, filmDAO);

        Field validationField = CatalogoService.class.getDeclaredField("validationManager");
        validationField.setAccessible(true);
        validationField.set(service, validationManager);

        locandinaValida = "img".getBytes();
    }

    @AfterEach
    void tearDown() {
        mockedDataSourceSingleton.close();
    }

    // -----------------------------------------------------------
    // Test: addFilmCatalogo()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldAddFilmSuccessfully() {
        when(validationManager.validate(anyMap())).thenReturn(true);
        when(filmDAO.create(any(Film.class))).thenReturn(true);

        assertDoesNotThrow(() ->
                service.addFilmCatalogo("Titolo", 120, "Descrizione",
                        locandinaValida, "Azione", "PG-13")
        );

        verify(validationManager, times(1)).addValidator(eq("titolo"), any(CampoValidator.class));
        verify(validationManager, times(1)).addValidator(eq("descrizione"), any(CampoValidator.class));
        verify(validationManager).validate(anyMap());
        verify(filmDAO).create(any(Film.class));
    }

    @RepeatedTest(5)
    void shouldThrowExceptionWhenAnyParameterIsInvalid() {
        // Titolo vuoto
        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("", 100, "desc", locandinaValida, "Azione", "PG-13"));
        // Durata <= 0
        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("Titolo", 0, "desc", locandinaValida, "Azione", "PG-13"));
        // Descrizione nulla
        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("Titolo", 100, null, locandinaValida, "Azione", "PG-13"));
        // Locandina nulla o vuota
        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("Titolo", 100, "desc", null, "Azione", "PG-13"));
        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("Titolo", 100, "desc", new byte[0], "Azione", "PG-13"));
        // Genere vuoto
        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("Titolo", 100, "desc", locandinaValida, "", "PG-13"));
        // Classificazione nulla
        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("Titolo", 100, "desc", locandinaValida, "Azione", null));

        // Classificazione vuota
        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("Titolo", 100, "desc", locandinaValida, "Azione", "")
        );

        // Genere nullo
        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("Titolo", 100, "desc", locandinaValida, null, "PG-13")
        );

        // Descrizione vuota
        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("Titolo", 100, "", locandinaValida, "Azione", "PG-13")
        );

        verifyNoInteractions(filmDAO);
    }

    @RepeatedTest(5)
    void shouldThrowExceptionWhenValidationFails() {
        when(validationManager.validate(anyMap())).thenReturn(false);

        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("Titolo", 120, "Descrizione", locandinaValida, "Azione", "PG-13"));

        verify(validationManager).addValidator(eq("titolo"), any(CampoValidator.class));
        verify(validationManager).addValidator(eq("descrizione"), any(CampoValidator.class));
        verify(validationManager).validate(anyMap());
        verify(filmDAO, never()).create(any());
    }

    @RepeatedTest(5)
    void shouldThrowRuntimeExceptionWhenFilmCreationFails() {
        when(validationManager.validate(anyMap())).thenReturn(true);
        when(filmDAO.create(any(Film.class))).thenReturn(false);

        RuntimeException ex = assertThrows(RuntimeException.class, () ->
                service.addFilmCatalogo("Titolo", 120, "Descrizione", locandinaValida, "Azione", "PG-13"));

        assertEquals("Errore durante l'inserimento del film nel catalogo.", ex.getMessage());
        verify(filmDAO).create(any(Film.class));
    }

    // -----------------------------------------------------------
    // Test: getCatalogo()
    // -----------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnCatalogoSuccessfully() {
        List<Film> expected = List.of(
                new Film(1, "Titolo1", "Genere", "PG-13", 120, locandinaValida, "Descrizione", false),
                new Film(2, "Titolo2", "Genere", "PG-13", 100, locandinaValida, "Descrizione2", false)
        );

        when(filmDAO.retrieveAll()).thenReturn(expected);

        List<Film> result = service.getCatalogo();

        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals("Titolo1", result.getFirst().getTitolo());
        verify(filmDAO).retrieveAll();
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenNoFilmsInCatalog() {
        when(filmDAO.retrieveAll()).thenReturn(Collections.emptyList());

        List<Film> result = service.getCatalogo();

        assertNotNull(result);
        assertTrue(result.isEmpty());
        verify(filmDAO).retrieveAll();
    }
}
