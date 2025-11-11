package integration.gestione_catena;

import integration.BaseIntegrationTest;
import it.unisa.application.sottosistemi.gestione_catena.view.VisualizzaCatalogoServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import java.util.List;

import static org.mockito.Mockito.*;

class VisualizzaCatalogoServletIT extends BaseIntegrationTest {

    public static class TestableVisualizzaCatalogoServlet extends VisualizzaCatalogoServlet {
        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp)
                throws jakarta.servlet.ServletException, java.io.IOException {
            super.doGet(req, resp);
        }
    }

    private TestableVisualizzaCatalogoServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servlet = new TestableVisualizzaCatalogoServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
    }

    @RepeatedTest(5)
    void visualizzaCatalogo_ok() throws Exception {
        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (1, 'Inception', 'Sci-Fi', 'T', 148, NULL, 'Sogni e realtà', TRUE);");

        when(request.getRequestDispatcher("/WEB-INF/jsp/catalogo.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("catalogo"), any(List.class));
        verify(dispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void visualizzaCatalogo_vuoto() throws Exception {
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"),any());
        verify(dispatcher).forward(request, response);
    }
}
