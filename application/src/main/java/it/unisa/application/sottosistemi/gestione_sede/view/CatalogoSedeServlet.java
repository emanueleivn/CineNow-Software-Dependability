package it.unisa.application.sottosistemi.gestione_sede.view;

import it.unisa.application.model.entity.Film;
import it.unisa.application.model.entity.Sede;
import it.unisa.application.sottosistemi.gestione_sede.service.ProgrammazioneSedeService;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;
import java.util.List;

@WebServlet("/Catalogo")
public class CatalogoSedeServlet extends HttpServlet {
    private static final int ITEMS_PER_PAGE = 9;

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        String sede = req.getParameter("sede");
        if (sede == null || sede.isBlank()) {
            req.setAttribute("errorMessage", "Errore caricamento catalogo: sede non specificata");
            req.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(req, resp);
            return;
        }
        Sede sedeObject;
        List<Film> catalogo;
        ProgrammazioneSedeService service = new ProgrammazioneSedeService();
        switch (sede) {
            case "Mercogliano":
                sedeObject = new Sede(1);
                catalogo = service.getCatalogoSede(sedeObject);
                req.setAttribute("sede", "Mercogliano");
                req.setAttribute("sedeId", sedeObject.getId());
                break;
            case "Laquila":
                sedeObject = new Sede(2);
                catalogo = service.getCatalogoSede(sedeObject);
                req.setAttribute("sede", "L'Aquila");
                req.setAttribute("sedeId", sedeObject.getId());
                break;
            default:
                req.setAttribute("errorMessage", "Errore caricamento catalogo");
                req.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(req, resp);
                return;
        }
        if (catalogo != null) {
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

            int totalItems = catalogo.size();
            int totalPages = (int) Math.ceil((double) totalItems / ITEMS_PER_PAGE);
            if (page > totalPages && totalPages > 0) page = totalPages;

            int startIndex = (page - 1) * ITEMS_PER_PAGE;
            int endIndex = Math.min(startIndex + ITEMS_PER_PAGE, totalItems);

            List<Film> paginatedCatalogo = catalogo.subList(startIndex, endIndex);

            req.setAttribute("catalogo", paginatedCatalogo);
            req.setAttribute("currentPage", page);
            req.setAttribute("totalPages", totalPages);
            req.getRequestDispatcher("/WEB-INF/jsp/catalogoSede.jsp").forward(req, resp);
        } else {
            req.setAttribute("errorMessage", "Errore caricamento catalogo");
            req.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(req, resp);
        }
    }
}
