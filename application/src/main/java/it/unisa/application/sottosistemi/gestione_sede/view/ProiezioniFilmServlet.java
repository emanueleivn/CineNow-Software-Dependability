package it.unisa.application.sottosistemi.gestione_sede.view;

import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.model.entity.Film;
import it.unisa.application.model.entity.Sede;
import it.unisa.application.model.dao.FilmDAO;
import it.unisa.application.model.dao.SedeDAO;
import it.unisa.application.sottosistemi.gestione_sede.service.ProgrammazioneSedeService;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

@WebServlet("/ProiezioniFilm")
public class ProiezioniFilmServlet extends HttpServlet {
    private static final Logger logger = Logger.getLogger(ProiezioniFilmServlet.class.getName());
    private static final int ITEMS_PER_PAGE = 7;

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        ProgrammazioneSedeService service = new ProgrammazioneSedeService();
        FilmDAO filmDAO = new FilmDAO();
        SedeDAO sedeDAO = new SedeDAO();

        try {
            int sedeId = Integer.parseInt(req.getParameter("sedeId"));
            int filmId = Integer.parseInt(req.getParameter("filmId"));
            List<Proiezione> programmazioneFilm = service.getProiezioniFilm(filmId, sedeId);
            Film film = filmDAO.retrieveById(filmId);
            Sede sede = sedeDAO.retrieveById(sedeId);

            if (film == null || sede == null || programmazioneFilm == null || programmazioneFilm.isEmpty()) {
                req.setAttribute("errorMessage", "Film o sede non trovati.");
                try {
                    req.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(req, resp);
                } catch (Exception e) {
                    logger.log(Level.SEVERE, "Errore durante il forward", e);
                }
                return;
            }

            // Paginazione
            int page = 1;
            String pageParam = req.getParameter("page");
            if (pageParam != null) {
                try {
                    page = Integer.parseInt(pageParam);
                    if (page < 1) page = 1;
                } catch (NumberFormatException e) {
                    page = 1;
                }
            }

            int totalItems = programmazioneFilm.size();
            int totalPages = (int) Math.ceil((double) totalItems / ITEMS_PER_PAGE);
            if (page > totalPages && totalPages > 0) page = totalPages;

            int startIndex = (page - 1) * ITEMS_PER_PAGE;
            int endIndex = Math.min(startIndex + ITEMS_PER_PAGE, totalItems);

            List<Proiezione> paginatedProiezioni = programmazioneFilm.subList(startIndex, endIndex);

            req.setAttribute("programmazioneFilm", paginatedProiezioni);
            req.setAttribute("filmNome", film.getTitolo());
            req.setAttribute("sedeNome", sede.getNome());
            req.setAttribute("filmId", filmId);
            req.setAttribute("sedeId", sedeId);
            req.setAttribute("currentPage", page);
            req.setAttribute("totalPages", totalPages);

            req.getRequestDispatcher("/WEB-INF/jsp/proiezioniFilm.jsp").forward(req, resp);
        } catch (ServletException | IOException e) {
            logger.log(Level.SEVERE, "Errore durante il recupero delle proiezioni", e);
            throw e;
        } catch (Exception e) {
            logger.log(Level.SEVERE, "Errore durante il recupero delle proiezioni", e);
            try {
                req.setAttribute("errorMessage", "Errore durante il recupero delle proiezioni: " + e.getMessage());
                throw ex;
            }
        }
    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        try {
            doGet(req, resp);
        } catch (ServletException | IOException e) {
    }
}
