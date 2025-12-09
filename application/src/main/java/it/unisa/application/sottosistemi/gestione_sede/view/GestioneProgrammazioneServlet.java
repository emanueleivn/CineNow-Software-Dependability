package it.unisa.application.sottosistemi.gestione_sede.view;

import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.sottosistemi.gestione_sede.service.ProgrammazioneSedeService;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.*;

import java.io.IOException;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

@WebServlet("/gestioneProgrammazione")
public class GestioneProgrammazioneServlet extends HttpServlet {
    private static final Logger logger = Logger.getLogger(GestioneProgrammazioneServlet.class.getName());
    private static final int ITEMS_PER_PAGE = 10;

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        try {
            int sedeId = Integer.parseInt(request.getParameter("sedeId"));
            ProgrammazioneSedeService service = new ProgrammazioneSedeService();
            List<Proiezione> programmazioni = service.getProgrammazione(sedeId);

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

            int totalItems = programmazioni.size();
            int totalPages = (int) Math.ceil((double) totalItems / ITEMS_PER_PAGE);
            if (page > totalPages && totalPages > 0) page = totalPages;

            int startIndex = (page - 1) * ITEMS_PER_PAGE;
            int endIndex = Math.min(startIndex + ITEMS_PER_PAGE, totalItems);

            List<Proiezione> paginatedProgrammazioni = programmazioni.subList(startIndex, endIndex);

            request.setAttribute("programmazioni", paginatedProgrammazioni);
            request.setAttribute("currentPage", page);
            request.setAttribute("totalPages", totalPages);
            request.setAttribute("sedeId", sedeId);
            request.getRequestDispatcher("/WEB-INF/jsp/gestioneProgrammazione.jsp").forward(request, response);
        } catch (NumberFormatException e) {
            logger.log(Level.SEVERE, "Parametro sedeId non valido.", e);
            response.sendError(HttpServletResponse.SC_BAD_REQUEST, "Parametro sedeId non valido.");
        } catch (Exception e) {
            logger.log(Level.SEVERE, "Errore durante il recupero delle proiezioni.", e);
            response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "Errore durante il recupero delle proiezioni.");
        }
    }
}
