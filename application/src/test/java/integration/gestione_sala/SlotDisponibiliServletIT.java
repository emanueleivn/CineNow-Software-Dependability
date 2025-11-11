package integration.gestione_sala;

import integration.BaseIntegrationTest;
import it.unisa.application.sottosistemi.gestione_sala.view.SlotDisponibiliServlet;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.sql.SQLException;
import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class SlotDisponibiliServletIT extends BaseIntegrationTest {

    public static class TestableSlotDisponibiliServlet extends SlotDisponibiliServlet {
        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp)
                throws ServletException, IOException {
            super.doGet(req, resp);
        }
    }

    private TestableSlotDisponibiliServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private StringWriter stringWriter;
    private PrintWriter writer;

    @BeforeEach
    void setup() throws SQLException, IOException {
        servlet = new TestableSlotDisponibiliServlet();

        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        stringWriter = new StringWriter();
        writer = new PrintWriter(stringWriter);

        when(response.getWriter()).thenReturn(writer);

        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Mercogliano', 'Via Roma 1', 'Avellino', '83100');");
        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100);");

        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (1, 'Inception', 'Sci-Fi', 'T', 148, NULL, 'Thriller', TRUE);");

        execute("INSERT INTO slot (id, ora_inizio) VALUES (1, '18:00:00');");
        execute("INSERT INTO slot (id, ora_inizio) VALUES (2, '21:00:00');");
    }

    @RepeatedTest(5)
    void doGet_successo() throws Exception {
        when(request.getParameter("filmId")).thenReturn("1");
        when(request.getParameter("salaId")).thenReturn("1");
        when(request.getParameter("dataInizio")).thenReturn(LocalDate.now().plusDays(1).toString());
        when(request.getParameter("dataFine")).thenReturn(LocalDate.now().plusDays(3).toString());

        servlet.doGet(request, response);

        verify(response).setContentType("application/json");
        writer.flush();

        String outputJson = stringWriter.toString();
        assertNotNull(outputJson);
        assertTrue(outputJson.contains("durataFilm"), "Il JSON deve contenere la chiave 'durataFilm'");
        assertTrue(outputJson.contains("calendar"), "Il JSON deve contenere la chiave 'calendar'");
    }

    @RepeatedTest(5)
    void doGet_filmNonEsistente() throws Exception {
        when(request.getParameter("filmId")).thenReturn("999"); // film non presente
        when(request.getParameter("salaId")).thenReturn("1");
        when(request.getParameter("dataInizio")).thenReturn(LocalDate.now().plusDays(1).toString());
        when(request.getParameter("dataFine")).thenReturn(LocalDate.now().plusDays(2).toString());

        servlet.doGet(request, response);

        verify(response).sendError(eq(HttpServletResponse.SC_BAD_REQUEST), any());
    }

    @RepeatedTest(5)
    void doGet_parametroMancante() throws Exception {
        when(request.getParameter("filmId")).thenReturn(null);
        when(request.getParameter("salaId")).thenReturn("1");
        when(request.getParameter("dataInizio")).thenReturn(LocalDate.now().plusDays(1).toString());
        when(request.getParameter("dataFine")).thenReturn(LocalDate.now().plusDays(2).toString());

        servlet.doGet(request, response);

        verify(response).sendError(eq(HttpServletResponse.SC_BAD_REQUEST), any());
    }

    @RepeatedTest(5)
    void doGet_parametroNonNumerico() throws Exception {
        when(request.getParameter("filmId")).thenReturn("abc"); // errore NumberFormatException
        when(request.getParameter("salaId")).thenReturn("1");
        when(request.getParameter("dataInizio")).thenReturn(LocalDate.now().plusDays(1).toString());
        when(request.getParameter("dataFine")).thenReturn(LocalDate.now().plusDays(2).toString());

        servlet.doGet(request, response);

        verify(response).sendError(eq(HttpServletResponse.SC_BAD_REQUEST), any());
    }

    @RepeatedTest(5)
    void doGet_dataNonValida() throws Exception {
        when(request.getParameter("filmId")).thenReturn("1");
        when(request.getParameter("salaId")).thenReturn("1");
        when(request.getParameter("dataInizio")).thenReturn("data-non-valida");
        when(request.getParameter("dataFine")).thenReturn(LocalDate.now().plusDays(2).toString());

        servlet.doGet(request, response);

        verify(response).sendError(eq(HttpServletResponse.SC_BAD_REQUEST), any());
    }

    @RepeatedTest(5)
    void doGet_slotVuoti() throws Exception {
        execute("DELETE FROM slot;");

        when(request.getParameter("filmId")).thenReturn("1");
        when(request.getParameter("salaId")).thenReturn("1");
        when(request.getParameter("dataInizio")).thenReturn(LocalDate.now().plusDays(1).toString());
        when(request.getParameter("dataFine")).thenReturn(LocalDate.now().plusDays(2).toString());

        servlet.doGet(request, response);

        verify(response).sendError(eq(HttpServletResponse.SC_BAD_REQUEST), any());
    }
}
