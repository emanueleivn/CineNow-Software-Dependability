package integration.gestione_sede;

import integration.BaseIntegrationTest;
import it.unisa.application.sottosistemi.gestione_sede.view.CatalogoSedeServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import java.io.IOException;
import java.sql.SQLException;

import static org.mockito.Mockito.*;

public class CatalogoSedeServletIT extends BaseIntegrationTest {

    public static class TestableCatalogoSedeServlet extends CatalogoSedeServlet {
        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
            super.doGet(req, resp);
        }
    }

    private TestableCatalogoSedeServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher catalogoDispatcher;
    private RequestDispatcher errorDispatcher;

    @BeforeEach
    void setup() throws SQLException {
        servlet = new TestableCatalogoSedeServlet();

        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        catalogoDispatcher = mock(RequestDispatcher.class);
        errorDispatcher = mock(RequestDispatcher.class);

        when(request.getRequestDispatcher("/WEB-INF/jsp/catalogoSede.jsp")).thenReturn(catalogoDispatcher);
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(errorDispatcher);

        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Mercogliano', 'Via Roma 1', 'Avellino', '83100');");
        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (2, 'Laquila', 'Via Firenze 2', 'L''Aquila', '67100');");

        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (1, 'Inception', 'Sci-Fi', 'T', 148, NULL, 'Thriller fantascientifico', TRUE);");
        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (2, 'Matrix', 'Azione', 'T', 136, NULL, 'Azione e realtà virtuale', TRUE);");

        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100);");
        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (2, 2, 1, 120);");

        execute("INSERT INTO slot (id, ora_inizio) VALUES (1, '18:00:00');");

        execute("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) VALUES (1, CURRENT_DATE, 1, 1, 1);");
        execute("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) VALUES (2, CURRENT_DATE, 2, 2, 1);");
    }

    @RepeatedTest(5)
    void catalogo_Mercogliano_ok() throws Exception {
        when(request.getParameter("sede")).thenReturn("Mercogliano");

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("sede"), eq("Mercogliano"));
        verify(request).setAttribute(eq("sedeId"), eq(1));
        verify(request).setAttribute(eq("catalogo"), any());
        verify(catalogoDispatcher).forward(request, response);
        verify(errorDispatcher, never()).forward(any(), any());
    }

    @RepeatedTest(5)
    void catalogo_LAquila_ok() throws Exception {
        when(request.getParameter("sede")).thenReturn("Laquila");

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("sede"), eq("L'Aquila"));
        verify(request).setAttribute(eq("sedeId"), eq(2));
        verify(request).setAttribute(eq("catalogo"), any());
        verify(catalogoDispatcher).forward(request, response);
        verify(errorDispatcher, never()).forward(any(), any());
    }

    @RepeatedTest(5)
    void sede_non_specificata() throws Exception {
        when(request.getParameter("sede")).thenReturn(null);

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
        verify(catalogoDispatcher, never()).forward(any(), any());
    }

    @RepeatedTest(5)
    void sede_inesistente() throws Exception {
        when(request.getParameter("sede")).thenReturn("Milano");

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"),any());
        verify(errorDispatcher).forward(request, response);
        verify(catalogoDispatcher, never()).forward(any(), any());
    }
}
