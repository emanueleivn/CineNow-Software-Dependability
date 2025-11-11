package integration.gestione_prenotazione;

import integration.BaseIntegrationTest;
import it.unisa.application.sottosistemi.gestione_prenotazione.view.SceltaPostoServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import java.sql.SQLException;

import static org.mockito.Mockito.*;

class SceltaPostoServletIT extends BaseIntegrationTest {

    public static class TestableSceltaPostoServlet extends SceltaPostoServlet {
        @Override
        public void doPost(HttpServletRequest req, HttpServletResponse resp)
                throws jakarta.servlet.ServletException, java.io.IOException {
            super.doPost(req, resp);
        }
    }

    private TestableSceltaPostoServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher piantinaDispatcher;
    private RequestDispatcher errorDispatcher;

    @BeforeEach
    void setup() throws SQLException {
        servlet = new TestableSceltaPostoServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        piantinaDispatcher = mock(RequestDispatcher.class);
        errorDispatcher = mock(RequestDispatcher.class);

        when(request.getRequestDispatcher("/WEB-INF/jsp/piantinaView.jsp")).thenReturn(piantinaDispatcher);
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(errorDispatcher);

        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Cinema', 'Via Roma', 'Avellino', '83100');");
        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100);");
        execute("INSERT INTO slot (id, ora_inizio) VALUES (1, '18:00:00');");
        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (1, 'Matrix', 'Sci-Fi', 'T', 130, NULL, 'Fantascienza', TRUE);");
        execute("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) " +
                "VALUES (1, CURRENT_DATE, 1, 1, 1);");
    }

    @RepeatedTest(5)
    void sceltaPosto_ok() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("1");
        servlet.doPost(request, response);
        verify(request).setAttribute(eq("postiProiezione"), any());
        verify(piantinaDispatcher).forward(request, response);
        verify(errorDispatcher, never()).forward(any(), any());
    }

    @RepeatedTest(5)
    void sceltaPosto_proiezioneInesistente() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("99");
        servlet.doPost(request, response);
        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void sceltaPosto_parametroNonValido() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("abc");
        servlet.doPost(request, response);
        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }
}
