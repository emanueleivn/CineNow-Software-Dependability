package integration.gestione_sala;

import integration.BaseIT;
import it.unisa.application.model.dao.FilmDAO;
import it.unisa.application.sottosistemi.gestione_sala.view.AggiungiProiezioneServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;
import org.mockito.MockedConstruction;

import java.io.IOException;
import java.sql.SQLException;
import java.time.LocalDate;

import static org.mockito.Mockito.*;

class AggiungiProiezioneServletIT extends BaseIT {

    public static class TestableAggiungiProiezioneServlet extends AggiungiProiezioneServlet {
        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
            super.doGet(req, resp);
        }

        @Override
        public void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
            super.doPost(req, resp);
        }
    }

    private TestableAggiungiProiezioneServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher successDispatcher;
    private RequestDispatcher errorDispatcher;

    @BeforeEach
    void setup() throws SQLException {
        servlet = new TestableAggiungiProiezioneServlet();

        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        successDispatcher = mock(RequestDispatcher.class);
        errorDispatcher = mock(RequestDispatcher.class);

        when(request.getRequestDispatcher("/WEB-INF/jsp/aggiungiProiezione.jsp")).thenReturn(successDispatcher);
        when(request.getRequestDispatcher("/WEB-INF/jsp/errore.jsp")).thenReturn(errorDispatcher);

        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Mercogliano', 'Via Roma 1', 'Avellino', '83100');");
        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (2, 'Laquila', 'Via Firenze 2', 'L''Aquila', '67100');");

        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100);");
        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (2, 2, 1, 120);");

        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (1, 'Inception', 'Sci-Fi', 'T', 148, NULL, 'Thriller', TRUE);");
        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (2, 'Matrix', 'Azione', 'T', 136, NULL, 'Realtà virtuale', TRUE);");

        execute("INSERT INTO slot (id, ora_inizio) VALUES (1, '18:00:00');");
        execute("INSERT INTO slot (id, ora_inizio) VALUES (2, '21:00:00');");
    }

    // ======================================
    // TEST DOGET - CASI POSITIVI
    // ======================================

    @RepeatedTest(5)
    void doGet_successo() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("1");

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("sedeId"), eq(1));
        verify(request).setAttribute(eq("films"), any());
        verify(request).setAttribute(eq("sale"), any());
        verify(successDispatcher).forward(request, response);
        //controllo errorDispatcher non chiamato
        verify(errorDispatcher, never()).forward(any(), any());
    }

    // ======================================
    // TEST DOGET - CASI DI ERRORE
    // ======================================

    @RepeatedTest(5)
    void doGet_parametroMancante() throws Exception {
        when(request.getParameter("sedeId")).thenReturn(null);

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void doGet_parametroNonNumerico() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("abc");

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void doGet_salaNonDisponibile() throws Exception {
        execute("DELETE FROM sala WHERE id_sede = 1;");
        when(request.getParameter("sedeId")).thenReturn("1");

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void doGet_filmNonDisponibile() throws Exception {
        execute("DELETE FROM film;");
        when(request.getParameter("sedeId")).thenReturn("1");

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    // ======================================
    // TEST DOPOST - CASI POSITIVI
    // ======================================

    @RepeatedTest(5)
    void doPost_successo() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("1");
        when(request.getParameter("film")).thenReturn("1");
        when(request.getParameter("sala")).thenReturn("1");
        when(request.getParameterValues("slot"))
                .thenReturn(new String[]{"1:" + LocalDate.now().plusDays(1)});

        servlet.doPost(request, response);

        verify(response).sendRedirect(contains("gestioneProgrammazione?sedeId=1"));
        //controllo sendRedirect verso errorDispatcher non chiamato
        verify(errorDispatcher, never()).forward(any(), any());
    }

    // ======================================
    // TEST DOPOST - CASI DI ERRORE
    // ======================================

    @RepeatedTest(5)
    void doPost_parametriMancanti() throws Exception {
        when(request.getParameter("sedeId")).thenReturn(null);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
        //controllo sendRedirect non chiamato
        verify(response, never()).sendRedirect(any());
    }

    @RepeatedTest(5)
    void doPost_slotNonSelezionato() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("1");
        when(request.getParameter("film")).thenReturn("1");
        when(request.getParameter("sala")).thenReturn("1");
        when(request.getParameterValues("slot")).thenReturn(null);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        //controllo sendRedirect non chiamato
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void doPost_proiezioneFallita() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("1");
        when(request.getParameter("film")).thenReturn("1");
        when(request.getParameter("sala")).thenReturn("1");
        when(request.getParameterValues("slot"))
                .thenReturn(new String[]{"1:" + LocalDate.now().minusDays(1)}); // data passata

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
        //controllo sendRedirect non chiamato
        verify(response, never()).sendRedirect(any());
    }

    @RepeatedTest(5)
    void doPost_slotMalformato() throws Exception {
        // Simuliamo parametri corretti tranne il valore di "slot"
        when(request.getParameter("sedeId")).thenReturn("1");
        when(request.getParameter("film")).thenReturn("1");
        when(request.getParameter("sala")).thenReturn("1");

        when(request.getParameterValues("slot")).thenReturn(new String[]{"abc:def"});

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
        verify(response, never()).sendRedirect(any());
    }
    // ======================================
    // TEST DOGET - RAMI FALSE
    // ======================================

    @RepeatedTest(5)
    void doGet_parametroVuoto() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("");  // stringa vuota

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void doGet_parametroVuotoConSpazi() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("   ");  // solo spazi

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void doGet_filmEmpty() throws Exception {
        execute("DELETE FROM film;");
        when(request.getParameter("sedeId")).thenReturn("1");
        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void doGet_saleNull() throws Exception {
        execute("DELETE FROM sala WHERE id_sede = 1;");
        when(request.getParameter("sedeId")).thenReturn("1");

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    // ======================================
    // TEST DOPOST - RAMI FALSE
    // ======================================

    @RepeatedTest(5)
    void doPost_parametroSedeVuoto() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("");  // stringa vuota
        when(request.getParameter("film")).thenReturn("1");
        when(request.getParameter("sala")).thenReturn("1");
        when(request.getParameterValues("slot"))
                .thenReturn(new String[]{"1:" + LocalDate.now().plusDays(1)});

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
        verify(response, never()).sendRedirect(any());
    }

    @RepeatedTest(5)
    void doPost_parametroSedeVuotoConSpazi() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("   ");  // solo spazi
        when(request.getParameter("film")).thenReturn("1");
        when(request.getParameter("sala")).thenReturn("1");
        when(request.getParameterValues("slot"))
                .thenReturn(new String[]{"1:" + LocalDate.now().plusDays(1)});

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
        verify(response, never()).sendRedirect(any());
    }

    @RepeatedTest(5)
    void doPost_slotArrayVuoto() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("1");
        when(request.getParameter("film")).thenReturn("1");
        when(request.getParameter("sala")).thenReturn("1");
        when(request.getParameterValues("slot")).thenReturn(new String[]{});  // array vuoto

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
        verify(response, never()).sendRedirect(any());
    }
}
