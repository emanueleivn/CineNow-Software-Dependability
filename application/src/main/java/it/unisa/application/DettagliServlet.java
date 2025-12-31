package it.unisa.application;

import it.unisa.application.model.dao.FilmDAO;
import it.unisa.application.model.entity.Film;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;

@WebServlet("/DettagliFilm")
public class DettagliServlet extends HttpServlet {
    private static final Logger logger = Logger.getLogger(DettagliServlet.class.getName());

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        try {
            String filmId = req.getParameter("filmId");
            String sedeId = req.getParameter("sedeId");
            FilmDAO filmDAO = new FilmDAO();

            int parsedFilmId;
            try {
                parsedFilmId = Integer.parseInt(filmId);
            } catch (NumberFormatException e) {
                logger.log(Level.WARNING, "Parametro filmId non valido: " + filmId, e);
                req.setAttribute("errorMessage", "ID film non valido.");
                try {
                    req.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(req, resp);
                } catch (Exception ex) {
                    logger.log(Level.SEVERE, "Errore durante il forward", ex);
                }
                return;
            }

            Film film = filmDAO.retrieveById(parsedFilmId);
            if (film != null) {
                req.setAttribute("film", film);
                req.setAttribute("sedeId", sedeId);
                req.getRequestDispatcher("/WEB-INF/jsp/dettagliFilm.jsp").forward(req, resp);
            } else {
                req.setAttribute("errorMessage", "Film non trovato.");
                req.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(req, resp);
            }
        } catch (ServletException | IOException e) {
            logger.log(Level.SEVERE, "Errore durante il recupero dei dettagli del film", e);
            req.setAttribute("errorMessage", "Errore durante il recupero dei dettagli");
            try {
                req.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(req, resp);
            } catch (Exception ex) {
                logger.log(Level.SEVERE, "Errore durante il forward alla pagina di errore", ex);
            }
}
