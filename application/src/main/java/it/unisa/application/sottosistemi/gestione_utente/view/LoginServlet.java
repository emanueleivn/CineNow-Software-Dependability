package it.unisa.application.sottosistemi.gestione_utente.view;

import it.unisa.application.model.entity.Utente;
import it.unisa.application.sottosistemi.gestione_utente.service.AutenticazioneService;
import it.unisa.application.utilities.InputSanitizer;
import jakarta.servlet.*;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.*;

import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;

@WebServlet("/login")
public class LoginServlet extends HttpServlet {
    private static final Logger logger = Logger.getLogger(LoginServlet.class.getName());
    private AutenticazioneService authService;

    @Override
    public void init() {
        authService = new AutenticazioneService();
    }

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        try {
            req.getRequestDispatcher("/WEB-INF/jsp/loginView.jsp").forward(req, resp);
        } catch (ServletException | IOException e) {
            logger.log(Level.SEVERE, "Errore durante il forward alla pagina di login", e);
            req.setAttribute("errorMessage", "Errore durante il caricamento della pagina di login");
            try {
                req.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(req, resp);
            } catch (Exception ex) {
                logger.log(Level.SEVERE, "Errore durante il forward alla pagina di errore", ex);
            }
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        try {
            String email = request.getParameter("email");
            String password = request.getParameter("password");

            // Validate input for safety before processing
            if (!InputSanitizer.isSafe(email) || !InputSanitizer.isSafe(password)) {
                request.setAttribute("errorMessage", "Input non valido rilevato");
                try {
                    request.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(request, response);
                } catch (Exception e) {
                    logger.log(Level.SEVERE, "Errore durante il forward", e);
                }
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
                        request.setAttribute("errorMessage", "Ruolo non riconosciuto");
                        try {
                            request.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(request, response);
                        } catch (Exception e) {
                            logger.log(Level.SEVERE, "Errore durante il forward", e);
                        }
                        break;
                }
            } else {
                request.setAttribute("errorMessage", "Formato non corretto o errore inserimento dati");
                try {
                    request.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(request, response);
                } catch (Exception e) {
                    logger.log(Level.SEVERE, "Errore durante il forward", e);
                }
            }
        } catch (Exception e) {
            logger.log(Level.SEVERE, "Errore durante il login", e);
            request.setAttribute("errorMessage", "Errore durante il login");
            try {
                request.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(request, response);
            } catch (Exception ex) {
                logger.log(Level.SEVERE, "Errore durante il forward alla pagina di errore", ex);
            }
        }
    }
}
