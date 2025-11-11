package integration.gestione_utente;

import integration.BaseIntegrationTest;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.sottosistemi.gestione_utente.view.RegistrazioneServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;
import org.mockito.MockedStatic;

import java.io.IOException;
import java.sql.SQLException;

import static org.mockito.Mockito.*;

public class RegistrazioneServletIT extends BaseIntegrationTest {

    public static class TestableRegistrazioneServlet extends RegistrazioneServlet {
        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
            super.doGet(req, resp);
        }

        @Override
        public void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
            super.doPost(req, resp);
        }
    }

    private TestableRegistrazioneServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setup() throws SQLException {
        servlet = new TestableRegistrazioneServlet();
        servlet.init();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);

        execute("INSERT INTO utente (email, password, ruolo) VALUES ('esistente@email.com', 'HASHED_pass', 'cliente');");
        execute("INSERT INTO cliente (email, nome, cognome) VALUES ('esistente@email.com', 'Mario', 'Rossi');");
    }

    @RepeatedTest(5)
    void testDoGet_forwardsToRegistrazioneView() throws ServletException, IOException {
        when(request.getRequestDispatcher("/WEB-INF/jsp/registrazioneView.jsp")).thenReturn(dispatcher);
        servlet.doGet(request, response);
        verify(dispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void testRegistrazioneValida_redirectsToHome() throws Exception {
        when(request.getParameter("email")).thenReturn("nuovo@email.com");
        when(request.getParameter("password")).thenReturn("password1");
        when(request.getParameter("nome")).thenReturn("Luca");
        when(request.getParameter("cognome")).thenReturn("Verdi");
        when(request.getSession()).thenReturn(session);

        try (MockedStatic<it.unisa.application.utilities.PasswordHash> mock = mockStatic(it.unisa.application.utilities.PasswordHash.class)) {
            mock.when(() -> it.unisa.application.utilities.PasswordHash.hash("password1")).thenReturn("HASHED_password1");
            servlet.doPost(request, response);
            verify(session).setAttribute(eq("cliente"), any(Cliente.class));
            verify(response).sendRedirect(contains("/Home"));
        }
    }

    @RepeatedTest(5)
    void testEmailEsistente_forwardsToErrorPage() throws Exception {
        when(request.getParameter("email")).thenReturn("esistente@email.com");
        when(request.getParameter("password")).thenReturn("password1");
        when(request.getParameter("nome")).thenReturn("Mario");
        when(request.getParameter("cognome")).thenReturn("Rossi");
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(dispatcher);

        try (MockedStatic<it.unisa.application.utilities.PasswordHash> mock = mockStatic(it.unisa.application.utilities.PasswordHash.class)) {
            mock.when(() -> it.unisa.application.utilities.PasswordHash.hash("password1")).thenReturn("HASHED_password1");
            servlet.doPost(request, response);
            verify(request).setAttribute(eq("errorMessage"), anyString());
            verify(dispatcher).forward(request, response);
        }
    }

    @RepeatedTest(5)
    void testEmailNonValida_forwardsToErrorPage() throws Exception {
        when(request.getParameter("email")).thenReturn("invalidemail");
        when(request.getParameter("password")).thenReturn("password1");
        when(request.getParameter("nome")).thenReturn("Mario");
        when(request.getParameter("cognome")).thenReturn("Rossi");
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(dispatcher);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), anyString());
        verify(dispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void testPasswordNonValida_forwardsToErrorPage() throws Exception {
        when(request.getParameter("email")).thenReturn("cliente@email.com");
        when(request.getParameter("password")).thenReturn("123");
        when(request.getParameter("nome")).thenReturn("Mario");
        when(request.getParameter("cognome")).thenReturn("Rossi");
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(dispatcher);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), anyString());
        verify(dispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void testCampiVuoti_forwardsToErrorPage() throws Exception {
        when(request.getParameter("email")).thenReturn("");
        when(request.getParameter("password")).thenReturn("");
        when(request.getParameter("nome")).thenReturn("");
        when(request.getParameter("cognome")).thenReturn("");
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(dispatcher);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), anyString());
        verify(dispatcher).forward(request, response);
    }
}
