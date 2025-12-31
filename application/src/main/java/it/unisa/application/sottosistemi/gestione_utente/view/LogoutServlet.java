package it.unisa.application.sottosistemi.gestione_utente.view;

import it.unisa.application.sottosistemi.gestione_utente.service.AutenticazioneService;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;

@WebServlet("/logout")
public class LogoutServlet extends HttpServlet {
    private static final Logger logger = Logger.getLogger(LogoutServlet.class.getName());
    private AutenticazioneService authService;

    @Override
    public void init() throws ServletException {
        authService = new AutenticazioneService();
    }

    @Override
    public void doGet(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        try {
            authService.logout(req.getSession());
            req.getRequestDispatcher("/Home").forward(req, resp);
        } catch (ServletException | IOException e) {
            logger.log(Level.SEVERE, "Errore durante il logout", e);
            throw e;
        }
    }
}
