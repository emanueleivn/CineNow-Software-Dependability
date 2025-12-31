package it.unisa.application;

import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;

@WebServlet("/Home")
public class HomeServlet extends HttpServlet {
    private static final Logger logger = Logger.getLogger(HomeServlet.class.getName());

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        try {
            req.getRequestDispatcher("/index.jsp").forward(req, resp);
        } catch (ServletException | IOException e) {
            logger.log(Level.SEVERE, "Errore durante il forward alla home page", e);
            req.setAttribute("errorMessage", "Errore durante il caricamento della home");
            try {
                req.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(req, resp);
            } catch (Exception ex) {
                logger.log(Level.SEVERE, "Errore durante il forward alla pagina di errore", ex);
            }
}
