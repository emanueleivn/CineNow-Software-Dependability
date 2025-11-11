package unit.test_entity;

import it.unisa.application.model.entity.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;
/**
 * Test di unità per la classe Sala.
 */
@ExtendWith(MockitoExtension.class)
class SalaTest {
    private Sala sala;

    @Mock
    private Sede sedeMock;

    @BeforeEach
    void setUp() {
        sedeMock = mock(Sede.class);
        sala = new Sala(10, 3, 120, sedeMock);
    }

    // ------------------------------------------------------------------------
    //                        TEST: aggiungiProiezione(...)
    // ------------------------------------------------------------------------

    @RepeatedTest(5)
    void shouldReturnSameProiezioniListReferenceAndNotAddNewItem() {
        Film film = mock(Film.class);
        Slot slot = mock(Slot.class);
        List<Proiezione> before = sala.getProiezioni();

        List<Proiezione> returned = sala.aggiungiProiezione(1, slot, LocalDate.now(), film);

        assertSame(before, returned);
        assertTrue(returned.isEmpty());
        assertTrue(sala.getProiezioni().isEmpty());
    }

    @RepeatedTest(5)
    void shouldNotThrowWhenPostiArePresentButProiezioniRemainUnchanged() {
        Film film = mock(Film.class);
        Slot slot = mock(Slot.class);

        List<Posto> posti = new ArrayList<>();
        posti.add(mock(Posto.class));
        posti.add(mock(Posto.class));
        sala.setPosti(posti);

        assertDoesNotThrow(() -> sala.aggiungiProiezione(2, slot, LocalDate.now(), film));
        assertTrue(sala.getProiezioni().isEmpty());
    }

    @RepeatedTest(5)
    void shouldNotThrowWhenPostiListIsEmpty() {
        sala.setPosti(new ArrayList<>());

        assertDoesNotThrow(() ->
                sala.aggiungiProiezione(3, mock(Slot.class), LocalDate.now(), mock(Film.class))
        );
        assertTrue(sala.getProiezioni().isEmpty());
    }

    // ------------------------------------------------------------------------
    //                        TEST: creaListaPosti(...)  (private)
    // ------------------------------------------------------------------------

    @RepeatedTest(5)
    void shouldCreatePostoProiezioneForEachPosto() throws Exception {
        Proiezione proiezione = mock(Proiezione.class);

        List<Posto> posti = new ArrayList<>();
        Posto p1 = mock(Posto.class);
        Posto p2 = mock(Posto.class);
        posti.add(p1);
        posti.add(p2);
        sala.setPosti(posti);

        Method m = Sala.class.getDeclaredMethod("creaListaPosti", Proiezione.class);
        m.setAccessible(true);

        @SuppressWarnings("unchecked")
        List<PostoProiezione> result = (List<PostoProiezione>) m.invoke(sala, proiezione);

        assertNotNull(result);
        assertEquals(posti.size(), result.size());
        assertNotNull(result.get(0));
        assertNotNull(result.get(1));

        Field postoField = PostoProiezione.class.getDeclaredField("posto");
        postoField.setAccessible(true);
        Field proiezioneField = PostoProiezione.class.getDeclaredField("proiezione");
        proiezioneField.setAccessible(true);

        assertSame(p1, postoField.get(result.get(0)));
        assertSame(p2, postoField.get(result.get(1)));
        assertSame(proiezione, proiezioneField.get(result.get(0)));
        assertSame(proiezione, proiezioneField.get(result.get(1)));
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenNoPosti() throws Exception {
        sala.setPosti(new ArrayList<>());
        Proiezione proiezione = mock(Proiezione.class);

        Method m = Sala.class.getDeclaredMethod("creaListaPosti", Proiezione.class);
        m.setAccessible(true);

        @SuppressWarnings("unchecked")
        List<PostoProiezione> result = (List<PostoProiezione>) m.invoke(sala, proiezione);

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }
}
