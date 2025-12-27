package it.unisa.application.sottosistemi.gestione_utente.view;

import it.unisa.application.model.entity.Utente;
import it.unisa.application.sottosistemi.gestione_utente.service.AutenticazioneService;
import it.unisa.application.utilities.InputSanitizer;
import jakarta.servlet.*;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.*;

import java.io.IOException;

@WebServlet("/login")
public class LoginServlet extends HttpServlet {
    private AutenticazioneService authService;

    @Override
    public void init() {
        authService = new AutenticazioneService();
    }

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        req.getRequestDispatcher("/WEB-INF/jsp/loginView.jsp").forward(req, resp);
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String email = request.getParameter("email");
        String password = request.getParameter("password");

        // Validate input for safety before processing
        if (!InputSanitizer.isSafe(email) || !InputSanitizer.isSafe(password)) {
            request.setAttribute("errorMessage", "Input non valido rilevato");
            request.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(request, response);
            return;
        }

        Utente utente = authService.login(email, password);
        if (utente != null) {
            // Sanitize user data before storing in session to prevent trust boundary violation
            Utente sanitizedUser = InputSanitizer.sanitizeUtente(utente);

            HttpSession session = request.getSession(true);
            String ruolo = sanitizedUser.getRuolo().toLowerCase();
            switch (ruolo) {
                case "cliente":
                    session.setAttribute("cliente", sanitizedUser);
                    response.sendRedirect(request.getContextPath() + "/Home");
                    break;
                case "gestore_sede":
                    session.setAttribute("gestoreSede", sanitizedUser);
                    response.sendRedirect(request.getContextPath() + "/areaGestoreSede.jsp");
                    break;
                case "gestore_catena":
                    session.setAttribute("gestoreCatena", sanitizedUser);
                    response.sendRedirect(request.getContextPath() + "/areaGestoreCatena.jsp");
                    break;
                default:
                    request.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(request, response);
                    break;
            }
        } else {
            request.setAttribute("errorMessage", "Formato non corretto o errore inserimento dati");
            request.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(request, response);
        }
    }
}
