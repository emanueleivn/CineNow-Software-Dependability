package integration.gestione_prenotazione;

import integration.BaseIT;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.sottosistemi.gestione_prenotazione.view.AggiungiOrdineServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;
import org.junit.jupiter.api.Test;

import java.sql.SQLException;

import static org.mockito.Mockito.*;

class AggiungiOrdineServletIT extends BaseIT {

    public static class TestableAggiungiOrdineServlet extends AggiungiOrdineServlet {
        @Override
        public void doPost(HttpServletRequest request, HttpServletResponse response)
                throws jakarta.servlet.ServletException, java.io.IOException {
            super.doPost(request, response);
        }
    }

    private TestableAggiungiOrdineServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher errorDispatcher;
    private Cliente cliente;

    @BeforeEach
    void setup() throws SQLException {
        servlet = new TestableAggiungiOrdineServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        errorDispatcher = mock(RequestDispatcher.class);

        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(errorDispatcher);
        when(request.getSession()).thenReturn(session);

        execute("INSERT INTO utente (email, password, ruolo) VALUES ('cliente@email.com', 'HASHED_pw', 'cliente');");
        execute("INSERT INTO cliente (email, nome, cognome) VALUES ('cliente@email.com', 'Mario', 'Rossi');");
        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Cinema', 'Via Roma', 'Avellino', '83100');");
        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100);");
        execute("INSERT INTO slot (id, ora_inizio) VALUES (1, '18:00:00');");
        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (1, 'Matrix', 'Sci-Fi', 'T', 130, NULL, 'Azione', TRUE);");
        execute("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) " +
                "VALUES (1, CURRENT_DATE, 1, 1, 1);");

        execute("INSERT INTO posto (id_sala, fila, numero) VALUES (1, 'A', 1);");
        execute("INSERT INTO posto (id_sala, fila, numero) VALUES (1, 'A', 2);");

        execute("INSERT INTO posto_proiezione (id_sala, fila, numero, id_proiezione, stato) " +
                "VALUES (1, 'A', 1, 1, TRUE);");
        execute("INSERT INTO posto_proiezione (id_sala, fila, numero, id_proiezione, stato) " +
                "VALUES (1, 'A', 2, 1, TRUE);");

        cliente = new Cliente("cliente@email.com", "HASHED_pw", "Mario", "Rossi");
    }

    @Test
    void aggiungiOrdine_ok() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("1");
        when(request.getParameter("posti")).thenReturn("A-1,A-2");
        when(request.getParameter("nomeCarta")).thenReturn("Mario Rossi");
        when(request.getParameter("numeroCarta")).thenReturn("1234567890123456");
        when(request.getParameter("scadenzaCarta")).thenReturn("12/27");
        when(request.getParameter("cvv")).thenReturn("123");
        when(session.getAttribute("cliente")).thenReturn(cliente);

        servlet.doPost(request, response);

        verify(response).sendRedirect(contains("/storicoOrdini"));
        verify(errorDispatcher, never()).forward(any(), any());
    }

    @RepeatedTest(5)
    void aggiungiOrdine_datiMancanti() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn(null);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void aggiungiOrdine_clienteNonInSessione() throws Exception {
        when(session.getAttribute("cliente")).thenReturn(null);
        when(request.getParameter("proiezioneId")).thenReturn("1");
        when(request.getParameter("posti")).thenReturn("A-1");
        when(request.getParameter("nomeCarta")).thenReturn("Mario Rossi");
        when(request.getParameter("numeroCarta")).thenReturn("123");
        when(request.getParameter("scadenzaCarta")).thenReturn("12/30");
        when(request.getParameter("cvv")).thenReturn("999");

        servlet.doPost(request, response);
        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void aggiungiOrdine_proiezioneInesistente() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("99");
        when(request.getParameter("posti")).thenReturn("A-1");
        when(request.getParameter("nomeCarta")).thenReturn("Mario Rossi");
        when(request.getParameter("numeroCarta")).thenReturn("1234567890123456");
        when(request.getParameter("scadenzaCarta")).thenReturn("12/27");
        when(request.getParameter("cvv")).thenReturn("123");
        when(session.getAttribute("cliente")).thenReturn(cliente);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @Test
    void aggiungiOrdine_postiMancanti() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("1");
        when(request.getParameter("posti")).thenReturn(null); // <– questo deve essere null
        when(request.getParameter("nomeCarta")).thenReturn("Mario Rossi");
        when(request.getParameter("numeroCarta")).thenReturn("1234567890123456");
        when(request.getParameter("scadenzaCarta")).thenReturn("12/27");
        when(request.getParameter("cvv")).thenReturn("123");
        when(session.getAttribute("cliente")).thenReturn(cliente);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @Test
    void aggiungiOrdine_nomeCartaMancante() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("1");
        when(request.getParameter("posti")).thenReturn("A-1");
        when(request.getParameter("nomeCarta")).thenReturn(null); // <–
        when(request.getParameter("numeroCarta")).thenReturn("1234567890123456");
        when(request.getParameter("scadenzaCarta")).thenReturn("12/27");
        when(request.getParameter("cvv")).thenReturn("123");
        when(session.getAttribute("cliente")).thenReturn(cliente);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @Test
    void aggiungiOrdine_numeroCartaMancante() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("1");
        when(request.getParameter("posti")).thenReturn("A-1");
        when(request.getParameter("nomeCarta")).thenReturn("Mario Rossi");
        when(request.getParameter("numeroCarta")).thenReturn(null); // <–
        when(request.getParameter("scadenzaCarta")).thenReturn("12/27");
        when(request.getParameter("cvv")).thenReturn("123");
        when(session.getAttribute("cliente")).thenReturn(cliente);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @Test
    void aggiungiOrdine_scadenzaMancante() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("1");
        when(request.getParameter("posti")).thenReturn("A-1");
        when(request.getParameter("nomeCarta")).thenReturn("Mario Rossi");
        when(request.getParameter("numeroCarta")).thenReturn("1234567890123456");
        when(request.getParameter("scadenzaCarta")).thenReturn(null); // <–
        when(request.getParameter("cvv")).thenReturn("123");
        when(session.getAttribute("cliente")).thenReturn(cliente);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @Test
    void aggiungiOrdine_cvvMancante() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("1");
        when(request.getParameter("posti")).thenReturn("A-1");
        when(request.getParameter("nomeCarta")).thenReturn("Mario Rossi");
        when(request.getParameter("numeroCarta")).thenReturn("1234567890123456");
        when(request.getParameter("scadenzaCarta")).thenReturn("12/27");
        when(request.getParameter("cvv")).thenReturn(null); // <–
        when(session.getAttribute("cliente")).thenReturn(cliente);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @Test
    void aggiungiOrdine_postoFormattatoMale_vieneIgnorato() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("1");
        // "A-1" è valido, "INVALID" genera parts.length == 1 (ramo false)
        when(request.getParameter("posti")).thenReturn("A-1,INVALID");
        when(request.getParameter("nomeCarta")).thenReturn("Mario Rossi");
        when(request.getParameter("numeroCarta")).thenReturn("1234567890123456");
        when(request.getParameter("scadenzaCarta")).thenReturn("12/27");
        when(request.getParameter("cvv")).thenReturn("123");
        when(session.getAttribute("cliente")).thenReturn(cliente);

        servlet.doPost(request, response);

        // L’ordine dovrebbe comunque andare a buon fine (almeno un posto valido)
        verify(response).sendRedirect(contains("/storicoOrdini"));
        verify(errorDispatcher, never()).forward(any(), any());
    }

}
