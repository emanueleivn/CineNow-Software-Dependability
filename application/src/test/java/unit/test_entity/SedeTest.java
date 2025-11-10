package unit.test_entity;

import it.unisa.application.model.entity.Film;
import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.model.entity.Sala;
import it.unisa.application.model.entity.Sede;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class SedeTest {

    private Sede sede;

    @Mock
    private Sala salaMock;

    @Mock
    private Proiezione proiezioneMock1;

    @Mock
    private Proiezione proiezioneMock2;

    @Mock
    private Film filmMock;

    @BeforeEach
    void setUp() {
        sede = new Sede(1, "Cinema Test", "Via Roma 10");
    }

    // ------------------------------------------------------------------------
    //                        TEST: getProgrammazione()
    // ------------------------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnAllProiezioniFromAllSale() {
        when(salaMock.getProiezioni()).thenReturn(List.of(proiezioneMock1, proiezioneMock2));
        sede.setSale(Set.of(salaMock));

        List<Proiezione> result = sede.getProgrammazione();

        assertEquals(2, result.size());
        assertTrue(result.contains(proiezioneMock1));
        assertTrue(result.contains(proiezioneMock2));
        verify(salaMock).getProiezioni();
    }

    @RepeatedTest(5)
    void shouldReturnEmptyProgrammazioneWhenNoSalePresent() {
        List<Proiezione> result = sede.getProgrammazione();

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    // ------------------------------------------------------------------------
    //                        TEST: getProiezioniFilm(Film)
    // ------------------------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnOnlyProiezioniMatchingFilm() {
        when(proiezioneMock1.getFilmProiezione()).thenReturn(filmMock);
        when(proiezioneMock2.getFilmProiezione()).thenReturn(mock(Film.class));
        when(salaMock.getProiezioni()).thenReturn(List.of(proiezioneMock1, proiezioneMock2));
        sede.setSale(Set.of(salaMock));

        List<Proiezione> result = sede.getProiezioniFilm(filmMock);

        assertEquals(1, result.size());
        assertTrue(result.contains(proiezioneMock1));
        assertFalse(result.contains(proiezioneMock2));
    }

    @RepeatedTest(5)
    void shouldHandleNullFilmProiezioneGracefully() {
        when(proiezioneMock1.getFilmProiezione()).thenReturn(null);
        when(salaMock.getProiezioni()).thenReturn(List.of(proiezioneMock1));
        sede.setSale(Set.of(salaMock));

        assertDoesNotThrow(() -> {
            List<Proiezione> result = sede.getProiezioniFilm(filmMock);
            assertNotNull(result);
            assertTrue(result.isEmpty());
        });
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenNoMatchingFilm() {
        when(proiezioneMock1.getFilmProiezione()).thenReturn(mock(Film.class));
        when(salaMock.getProiezioni()).thenReturn(List.of(proiezioneMock1));
        sede.setSale(Set.of(salaMock));

        List<Proiezione> result = sede.getProiezioniFilm(filmMock);

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @RepeatedTest(5)
    void shouldHandleNullFilmParameterGracefully() {
        when(proiezioneMock1.getFilmProiezione()).thenReturn(filmMock);
        when(salaMock.getProiezioni()).thenReturn(List.of(proiezioneMock1));
        sede.setSale(Set.of(salaMock));

        assertDoesNotThrow(() -> {
            List<Proiezione> result = sede.getProiezioniFilm(null);
            assertNotNull(result);
            assertTrue(result.isEmpty());
        });
    }
}
