package integration.gestione_prenotazione;

import integration.BaseIntegrationTest;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.sottosistemi.gestione_prenotazione.view.StoricoOrdiniServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import java.sql.SQLException;

import static org.mockito.Mockito.*;

class StoricoOrdiniServletIT extends BaseIntegrationTest {

    public static class TestableStoricoOrdiniServlet extends StoricoOrdiniServlet {
        @Override
        public void doGet(HttpServletRequest request, HttpServletResponse response)
                throws jakarta.servlet.ServletException, java.io.IOException {
            super.doGet(request, response);
        }
    }

    private TestableStoricoOrdiniServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher storicoDispatcher;
    private RequestDispatcher errorDispatcher;
    private Cliente cliente;

    @BeforeEach
    void setup() throws SQLException {
        servlet = new TestableStoricoOrdiniServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        storicoDispatcher = mock(RequestDispatcher.class);
        errorDispatcher = mock(RequestDispatcher.class);

        when(request.getSession()).thenReturn(session);
        when(request.getRequestDispatcher("/WEB-INF/jsp/storicoOrdini.jsp")).thenReturn(storicoDispatcher);
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(errorDispatcher);

        execute("INSERT INTO utente (email, password, ruolo) VALUES ('cliente@email.com', 'HASHED_pw', 'cliente');");
        execute("INSERT INTO cliente (email, nome, cognome) VALUES ('cliente@email.com', 'Mario', 'Rossi');");
        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Cinema', 'Via Roma', 'Avellino', '83100');");
        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100);");
        execute("INSERT INTO slot (id, ora_inizio) VALUES (1, '18:00:00');");
        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (1, 'Inception', 'Sci-Fi', 'T', 148, NULL, 'Thriller', TRUE);");
        execute("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) " +
                "VALUES (1, CURRENT_DATE, 1, 1, 1);");
        execute("INSERT INTO prenotazione (id, email_cliente, id_proiezione) VALUES (1, 'cliente@email.com', 1);");

        cliente = new Cliente("cliente@email.com", "HASHED_pw", "Mario", "Rossi");
    }

    @RepeatedTest(5)
    void storicoOrdini_ok() throws Exception {
        when(session.getAttribute("cliente")).thenReturn(cliente);
        servlet.doGet(request, response);
        verify(request).setAttribute(eq("storico"), any());
        verify(storicoDispatcher).forward(request, response);
        verify(errorDispatcher, never()).forward(any(), any());
    }

    @RepeatedTest(5)
    void storicoOrdini_clienteNonInSessione() throws Exception {
        when(session.getAttribute("cliente")).thenReturn(null);
        servlet.doGet(request, response);
        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
        verify(storicoDispatcher, never()).forward(any(), any());
    }
}
