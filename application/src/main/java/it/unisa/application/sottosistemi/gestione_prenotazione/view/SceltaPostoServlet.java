package it.unisa.application.sottosistemi.gestione_prenotazione.view;

import it.unisa.application.model.entity.PostoProiezione;
import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.sottosistemi.gestione_prenotazione.service.PrenotazioneService;
import it.unisa.application.model.dao.ProiezioneDAO;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

@WebServlet("/SceltaPosto")
public class SceltaPostoServlet extends HttpServlet {
    private static final Logger logger = Logger.getLogger(SceltaPostoServlet.class.getName());
    private final PrenotazioneService prenotazioneService = new PrenotazioneService();
    private final ProiezioneDAO proiezioneDAO = new ProiezioneDAO();

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        try {
            int proiezioneId = Integer.parseInt(req.getParameter("proiezioneId"));
            Proiezione proiezione = proiezioneDAO.retrieveById(proiezioneId);
            if (proiezione == null) {
                req.setAttribute("errorMessage", "Proiezione non trovata.");
                try {
                    req.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(req, resp);
                } catch (Exception e) {
                    logger.log(Level.SEVERE, "Errore durante il forward", e);
                }
                return;
            }
            List<PostoProiezione> postiProiezione = prenotazioneService.ottieniPostiProiezione(proiezione);
            req.setAttribute("postiProiezione", postiProiezione);
            req.setAttribute("proiezione", proiezione);
            req.getRequestDispatcher("/WEB-INF/jsp/piantinaView.jsp").forward(req, resp);

        } catch (NumberFormatException e) {
            logger.log(Level.WARNING, "Parametro proiezioneId non valido", e);
            try {
                req.setAttribute("errorMessage", "Parametro non valido.");
                req.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(req, resp);
            } catch (ServletException | IOException ex) {
                logger.log(Level.SEVERE, "Errore durante il forward alla pagina di errore", ex);
            }
        } catch (ServletException | IOException e) {
            logger.log(Level.SEVERE, "Errore durante il recupero dei posti", e);
            req.setAttribute("errorMessage", "Errore durante il recupero dei posti.");
            try {
                req.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(req, resp);
            } catch (ServletException | IOException ex) {
                logger.log(Level.SEVERE, "Errore durante il forward alla pagina di errore", ex);
            }
        } catch (Exception e) {
            logger.log(Level.SEVERE, "Errore durante il recupero dei posti", e);
            try {
                req.setAttribute("errorMessage", "Errore durante il recupero dei posti.");
                req.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(req, resp);
            } catch (Exception ex) {
                logger.log(Level.SEVERE, "Errore durante il forward alla pagina di errore", ex);
            }
        }
    }
}
