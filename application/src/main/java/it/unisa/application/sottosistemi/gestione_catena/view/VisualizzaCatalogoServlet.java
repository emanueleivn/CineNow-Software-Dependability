package it.unisa.application.sottosistemi.gestione_catena.view;

import it.unisa.application.model.entity.Film;
import it.unisa.application.sottosistemi.gestione_catena.service.CatalogoService;

import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

@WebServlet("/catalogo")
public class VisualizzaCatalogoServlet extends HttpServlet {
    private static final Logger logger = Logger.getLogger(VisualizzaCatalogoServlet.class.getName());
    private static final int ITEMS_PER_PAGE = 9;
    private final CatalogoService catalogoService = new CatalogoService();

    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        try {
            List<Film> catalogo = catalogoService.getCatalogo();
            if (catalogo.isEmpty()) {
                request.setAttribute("errorMessage", "Nessun film trovato.");
                request.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(request, response);
            } else {
                // Paginazione
                int page = 1;
                String pageParam = request.getParameter("page");
                if (pageParam != null) {
                    try {
                        page = Integer.parseInt(pageParam);
                        if (page < 1) page = 1;
                    } catch (NumberFormatException e) {
                        page = 1;
                    }
                }

                int totalItems = catalogo.size();
                int totalPages = (int) Math.ceil((double) totalItems / ITEMS_PER_PAGE);
                if (page > totalPages && totalPages > 0) page = totalPages;

                int startIndex = (page - 1) * ITEMS_PER_PAGE;
                int endIndex = Math.min(startIndex + ITEMS_PER_PAGE, totalItems);

                List<Film> paginatedCatalogo = catalogo.subList(startIndex, endIndex);

                request.setAttribute("catalogo", paginatedCatalogo);
                request.setAttribute("currentPage", page);
                request.setAttribute("totalPages", totalPages);
                request.getRequestDispatcher("/WEB-INF/jsp/catalogo.jsp").forward(request, response);
            }
        } catch (Exception e) {
            logger.log(Level.SEVERE, "Errore durante il caricamento del catalogo", e);
            request.setAttribute("errorMessage", "Errore durante il caricamento del catalogo");
            try {
                request.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(request, response);
            } catch (Exception ex) {
                logger.log(Level.SEVERE, "Errore durante il forward alla pagina di errore", ex);
            }
        }
    }
}
