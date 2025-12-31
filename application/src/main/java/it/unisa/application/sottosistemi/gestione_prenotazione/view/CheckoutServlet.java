package it.unisa.application.sottosistemi.gestione_prenotazione.view;

import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;

@WebServlet("/Checkout")
public class CheckoutServlet extends HttpServlet {
    private static final Logger logger = Logger.getLogger(CheckoutServlet.class.getName());

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        try {
            String proiezioneId = request.getParameter("proiezioneId");
            String posti = request.getParameter("posti");
            String totale = request.getParameter("totale");
            if (proiezioneId == null || posti == null || totale == null
                    || proiezioneId.isBlank() || posti.isBlank() || totale.isBlank()) {
                request.setAttribute("errorMessage", "Dati checkout mancanti o non validi.");
                try {
                    request.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(request, response);
                } catch (Exception e) {
                    logger.log(Level.SEVERE, "Errore durante il forward", e);
                }
                return;
            }
            request.setAttribute("proiezioneId", proiezioneId);
            request.setAttribute("posti", posti);
            request.setAttribute("totale", totale);
            request.getRequestDispatcher("/WEB-INF/jsp/checkout.jsp").forward(request, response);
        } catch (ServletException | IOException e) {
            logger.log(Level.SEVERE, "Errore durante il checkout", e);
            request.setAttribute("errorMessage", "Errore durante il checkout");
            try {
                request.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(request, response);
            } catch (Exception ex) {
                logger.log(Level.SEVERE, "Errore durante il forward alla pagina di errore", ex);
            }
}
