package integration.gestione_utente;

import integration.BaseIntegrationTest;
import it.unisa.application.model.entity.GestoreSede;
import it.unisa.application.model.entity.Utente;
import it.unisa.application.sottosistemi.gestione_utente.view.LoginServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import java.io.IOException;
import java.sql.SQLException;

import static org.mockito.Mockito.*;

public class LoginServletIT extends BaseIntegrationTest {

    public static class TestableLoginServlet extends LoginServlet {
        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
            super.doGet(req, resp);
        }

        @Override
        public void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
            super.doPost(req, resp);
        }
    }

    private TestableLoginServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setup() throws SQLException {
        servlet = new TestableLoginServlet();
        servlet.init();

        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);

        execute("INSERT INTO utente (email, password, ruolo) VALUES ('cliente1@email.com', 'HASHED_password1', 'cliente');");
        execute("INSERT INTO cliente (email, nome, cognome) VALUES ('cliente1@email.com', 'Mario', 'Rossi');");
        execute("INSERT INTO utente (email, password, ruolo) VALUES ('gestore@email.com', 'HASHED_gestore', 'gestore_sede');");
        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Cinema Centro', 'Via Roma 1', 'Napoli', '80100');");
        execute("INSERT INTO gest_sede (email, id_sede) VALUES ('gestore@email.com', 1);");
        execute("INSERT INTO utente (email, password, ruolo) VALUES ('catena@email.com', 'HASHED_catena', 'gestore_catena');");
    }

    @RepeatedTest(5)
    void testDoGet_forwardsToLoginView() throws ServletException, IOException {
        when(request.getRequestDispatcher("/WEB-INF/jsp/loginView.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void testLoginCliente_redirectsToHome() throws Exception {
        when(request.getParameter("email")).thenReturn("cliente1@email.com");
        when(request.getParameter("password")).thenReturn("password1");
        when(request.getSession(true)).thenReturn(session);

        try (var mocked = mockStatic(it.unisa.application.utilities.PasswordHash.class)) {
            mocked.when(() -> it.unisa.application.utilities.PasswordHash.hash("password1"))
                    .thenReturn("HASHED_password1");

            servlet.doPost(request, response);

            verify(session).setAttribute(eq("cliente"), any(Utente.class));
            verify(response).sendRedirect(contains("/Home"));
        }
    }

    @RepeatedTest(5)
    void testLoginGestore_redirectsToAreaGestoreSede() throws Exception {
        when(request.getParameter("email")).thenReturn("gestore@email.com");
        when(request.getParameter("password")).thenReturn("gestore");
        when(request.getSession(true)).thenReturn(session);

        try (var mocked = mockStatic(it.unisa.application.utilities.PasswordHash.class)) {
            mocked.when(() -> it.unisa.application.utilities.PasswordHash.hash("gestore"))
                    .thenReturn("HASHED_gestore");

            servlet.doPost(request, response);

            verify(session).setAttribute(eq("gestoreSede"), any(GestoreSede.class));
            verify(response).sendRedirect(contains("/areaGestoreSede.jsp"));
        }
    }

    @RepeatedTest(5)
    void testLoginGestoreCatena_redirectsToAreaGestoreCatena() throws Exception {
        when(request.getParameter("email")).thenReturn("catena@email.com");
        when(request.getParameter("password")).thenReturn("catena");
        when(request.getSession(true)).thenReturn(session);

        try (var mocked = mockStatic(it.unisa.application.utilities.PasswordHash.class)) {
            mocked.when(() -> it.unisa.application.utilities.PasswordHash.hash("catena"))
                    .thenReturn("HASHED_catena");

            servlet.doPost(request, response);

            verify(session).setAttribute(eq("gestoreCatena"), any(Utente.class));
            verify(response).sendRedirect(contains("/areaGestoreCatena.jsp"));
        }
    }

    @RepeatedTest(5)
    void testLoginFallito_forwardsToErrorPage() throws Exception {
        when(request.getParameter("email")).thenReturn("wrong@email.com");
        when(request.getParameter("password")).thenReturn("invalid");
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(dispatcher);

        try (var mocked = mockStatic(it.unisa.application.utilities.PasswordHash.class)) {
            mocked.when(() -> it.unisa.application.utilities.PasswordHash.hash("invalid"))
                    .thenReturn("HASHED_invalid");

            servlet.doPost(request, response);

            verify(request).setAttribute(eq("errorMessage"), anyString());
            verify(dispatcher).forward(request, response);
        }
    }
}
