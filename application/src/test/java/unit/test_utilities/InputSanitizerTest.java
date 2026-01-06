package unit.test_utilities;

import it.unisa.application.model.entity.Cliente;
import it.unisa.application.model.entity.GestoreSede;
import it.unisa.application.model.entity.Sede;
import it.unisa.application.model.entity.Utente;
import it.unisa.application.utilities.InputSanitizer;
import org.junit.jupiter.api.RepeatedTest;

import static org.junit.jupiter.api.Assertions.*;

public class InputSanitizerTest {

    // -------------------------
    // Tests: sanitize(String)
    // -------------------------

    @RepeatedTest(5)
    void testSanitize_NullReturnsNull() {
        assertNull(InputSanitizer.sanitize(null));
    }

    @RepeatedTest(5)
    void testSanitize_TrimsWhitespace() {
        String input = "   Mario Rossi   ";
        String sanitized = InputSanitizer.sanitize(input);

        assertEquals("Mario Rossi", sanitized);
    }

    @RepeatedTest(5)
    void testSanitize_EncodesHtmlSpecialChars() {
        String input = "a&b<c>d\"e'f/g";
        String sanitized = InputSanitizer.sanitize(input);

        // Attenzione: l'ordine dei replace conta: prima '&' poi gli altri
        assertEquals("a&amp;b&lt;c&gt;d&quot;e&#x27;f&#x2F;g", sanitized);
    }

    @RepeatedTest(5)
    void testSanitize_AlreadySanitizedAmpersand_IsDoubleEncoded() {
        // Questo test documenta il comportamento attuale (non idempotente).
        // Se in futuro vuoi evitare double-encoding, dovrai cambiare implementazione.
        String input = "&lt;test&gt;";
        String sanitized = InputSanitizer.sanitize(input);

        assertEquals("&amp;lt;test&amp;gt;", sanitized);
    }

    @RepeatedTest(5)
    void testSanitize_EmptyStringRemainsEmpty() {
        assertEquals("", InputSanitizer.sanitize(""));
        assertEquals("", InputSanitizer.sanitize("   "));
    }

    // -------------------------
    // Tests: isSafe(String)
    // -------------------------

    @RepeatedTest(5)
    void testIsSafe_NullReturnsTrue() {
        assertTrue(InputSanitizer.isSafe(null));
    }

    @RepeatedTest(5)
    void testIsSafe_SafeTextReturnsTrue() {
        assertTrue(InputSanitizer.isSafe("Mario Rossi"));
        assertTrue(InputSanitizer.isSafe("test@example.com"));
        assertTrue(InputSanitizer.isSafe("descrizione innocua 123"));
    }

    @RepeatedTest(5)
    void testIsSafe_DetectsScriptTag_CaseInsensitive() {
        assertFalse(InputSanitizer.isSafe("<script>alert(1)</script>"));
        assertFalse(InputSanitizer.isSafe("<ScRiPt>alert(1)</ScRiPt>"));
    }

    @RepeatedTest(5)
    void testIsSafe_DetectsJavascriptProtocol() {
        assertFalse(InputSanitizer.isSafe("javascript:alert(1)"));
        assertFalse(InputSanitizer.isSafe("JaVaScRiPt:alert(1)"));
    }

    @RepeatedTest(5)
    void testIsSafe_DetectsEventHandlers() {
        assertFalse(InputSanitizer.isSafe("img src=x onerror=alert(1)"));
        assertFalse(InputSanitizer.isSafe("body onload=doSomething()"));
        assertFalse(InputSanitizer.isSafe("div onclick=evil()"));
        assertFalse(InputSanitizer.isSafe("a onmouseover=evil()"));
    }

    @RepeatedTest(5)
    void testIsSafe_DetectsEvalExpressionVbscript() {
        assertFalse(InputSanitizer.isSafe("eval(alert(1))"));
        assertFalse(InputSanitizer.isSafe("expression(alert(1))"));
        assertFalse(InputSanitizer.isSafe("vbscript:msgbox(\"x\")"));
    }

    // -------------------------
    // Tests: sanitizeUtente(Utente)
    // -------------------------

    @RepeatedTest(5)
    void testSanitizeUtente_NullReturnsNull() {
        assertNull(InputSanitizer.sanitizeUtente(null));
    }

    @RepeatedTest(5)
    void testSanitizeUtente_Cliente_IsSanitizedAndTypePreserved() {
        Cliente cliente = new Cliente(
                "  a&b<c>@mail.com  ",
                "HASHED_PASSWORD",
                "  Ma<rio  ",
                "  Ros&si  "
        );
        cliente.setRuolo("  USER<script>  ");

        Utente sanitized = InputSanitizer.sanitizeUtente(cliente);

        assertNotNull(sanitized);
        assertTrue(sanitized instanceof Cliente);

        Cliente sanitizedCliente = (Cliente) sanitized;

        // email, nome, cognome e ruolo sanitizzati
        assertEquals("a&amp;b&lt;c&gt;@mail.com", sanitizedCliente.getEmail());
        assertEquals("Ma&lt;rio", sanitizedCliente.getNome());
        assertEquals("Ros&amp;si", sanitizedCliente.getCognome());
        assertEquals("USER&lt;script&gt;", sanitizedCliente.getRuolo());

        // password non deve essere sanitizzata (resta invariata)
        assertEquals("HASHED_PASSWORD", sanitizedCliente.getPassword());
    }

    @RepeatedTest(5)
    void testSanitizeUtente_GestoreSede_IsSanitizedAndTypePreserved_SedeUnchanged() {
        Sede sedeTrusted= new Sede(1);

        GestoreSede gestore = new GestoreSede(
                "  gestore<1>@mail.com  ",
                "HASHED_PASSWORD",
                sedeTrusted
        );
        gestore.setRuolo("  ADMIN\"  ");

        Utente sanitized = InputSanitizer.sanitizeUtente(gestore);

        assertNotNull(sanitized);
        assertTrue(sanitized instanceof GestoreSede);

        GestoreSede sanitizedGestore = (GestoreSede) sanitized;

        assertEquals("gestore&lt;1&gt;@mail.com", sanitizedGestore.getEmail());
        assertEquals("ADMIN&quot;", sanitizedGestore.getRuolo());
        assertEquals("HASHED_PASSWORD", sanitizedGestore.getPassword());

        assertSame(sedeTrusted, sanitizedGestore.getSede());
    }

    @RepeatedTest(5)
    void testSanitizeUtente_BaseUtente_IsSanitizedAndTypePreserved() {
        Utente utente = new Utente(
                "  user'@mail.com  ",
                "HASHED_PASSWORD",
                "  RUOLO/TEST  "
        );

        Utente sanitized = InputSanitizer.sanitizeUtente(utente);

        assertNotNull(sanitized);
        assertEquals(Utente.class, sanitized.getClass());

        assertEquals("user&#x27;@mail.com", sanitized.getEmail());
        assertEquals("RUOLO&#x2F;TEST", sanitized.getRuolo());
        assertEquals("HASHED_PASSWORD", sanitized.getPassword());
    }

    @RepeatedTest(5)
    void testSanitizeUtente_DoesNotMutateOriginalObject() {
        Cliente cliente = new Cliente(
                " a<b>@mail.com ",
                "HASHED_PASSWORD",
                " Nome ",
                " Cognome "
        );
        cliente.setRuolo(" ROLE ");

        Utente sanitized = InputSanitizer.sanitizeUtente(cliente);

        // Verifica che l'oggetto originale NON sia stato alterato
        assertEquals(" a<b>@mail.com ", cliente.getEmail());
        assertEquals(" Nome ", cliente.getNome());
        assertEquals(" Cognome ", cliente.getCognome());
        assertEquals(" ROLE ", cliente.getRuolo());

        assertNotSame(cliente, sanitized);
    }
}
