package integration.gestione_sede;

import integration.BaseIntegrationTest;
import it.unisa.application.sottosistemi.gestione_sede.view.GestioneProgrammazioneServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import java.io.IOException;
import java.sql.SQLException;

import static org.mockito.Mockito.*;

public class GestioneProgrammazioneServletIT extends BaseIntegrationTest {

    public static class TestableGestioneProgrammazioneServlet extends GestioneProgrammazioneServlet {
        @Override
        protected void doGet(HttpServletRequest req, HttpServletResponse resp)
                throws ServletException, IOException {
            super.doGet(req, resp);
        }
    }

    private TestableGestioneProgrammazioneServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setup() throws SQLException {
        servlet = new TestableGestioneProgrammazioneServlet();

        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);

        when(request.getRequestDispatcher("/WEB-INF/jsp/gestioneProgrammazione.jsp"))
                .thenReturn(dispatcher);

        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Mercogliano', 'Via Roma 1', 'Avellino', '83100');");
        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (2, 'Laquila', 'Via Firenze 2', 'L''Aquila', '67100');");

        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (1, 'Inception', 'Sci-Fi', 'T', 148, NULL, 'Thriller fantascientifico', TRUE);");
        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (2, 'Matrix', 'Azione', 'T', 136, NULL, 'Azione e realtà virtuale', TRUE);");

        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100);");
        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (2, 2, 1, 120);");

        execute("INSERT INTO slot (id, ora_inizio) VALUES (1, '18:00:00');");
        execute("INSERT INTO slot (id, ora_inizio) VALUES (2, '21:00:00');");

        execute("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) VALUES (1, CURRENT_DATE, 1, 1, 1);");
        execute("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) VALUES (2, CURRENT_DATE, 2, 2, 2);");
    }

    @RepeatedTest(5)
    void programmazione_Mercogliano_ok() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("1");

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("programmazioni"), any());
        verify(dispatcher).forward(request, response);
        verify(response, never()).sendError(anyInt(), anyString());
    }

    @RepeatedTest(5)
    void programmazione_LAquila_ok() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("2");

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("programmazioni"), any());
        verify(dispatcher).forward(request, response);
        verify(response, never()).sendError(anyInt(), anyString());
    }

    @RepeatedTest(5)
    void sede_non_valida() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("abc");

        servlet.doGet(request, response);

        verify(response).sendError(eq(HttpServletResponse.SC_BAD_REQUEST), any());
        verify(dispatcher, never()).forward(any(), any());
    }

    @RepeatedTest(5)
    void sede_inesistente() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("999");

        servlet.doGet(request, response);
        verify(request).setAttribute(eq("programmazioni"), any());
        verify(dispatcher).forward(request, response);
        verify(response, never()).sendError(anyInt(), anyString());
    }
}
