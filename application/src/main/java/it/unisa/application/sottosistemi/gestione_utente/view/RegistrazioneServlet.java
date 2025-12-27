package it.unisa.application.sottosistemi.gestione_utente.view;

import it.unisa.application.model.entity.Cliente;
import it.unisa.application.sottosistemi.gestione_utente.service.RegistrazioneService;
import it.unisa.application.utilities.InputSanitizer;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.io.IOException;
@WebServlet("/registrazione")
public class RegistrazioneServlet extends HttpServlet {
    RegistrazioneService regServ;

    @Override
    public void init() {
        regServ = new RegistrazioneService();
    }

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        req.getRequestDispatcher("/WEB-INF/jsp/registrazioneView.jsp").forward(req, resp);
    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        String email = req.getParameter("email");
        String password = req.getParameter("password");
        String nome = req.getParameter("nome");
        String cognome = req.getParameter("cognome");

        // Validate input for safety before processing
        if (!InputSanitizer.isSafe(email) || !InputSanitizer.isSafe(password) ||
            !InputSanitizer.isSafe(nome) || !InputSanitizer.isSafe(cognome)) {
            req.setAttribute("errorMessage", "Input non valido rilevato");
            req.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(req, resp);
            return;
        }

        Cliente cliente = regServ.registrazione(email, password, nome, cognome);
        if(cliente!=null){
            // Sanitize user data before storing in session to prevent trust boundary violation
            Cliente sanitizedCliente = (Cliente) InputSanitizer.sanitizeUtente(cliente);

            HttpSession session = req.getSession();
            session.setAttribute("cliente", sanitizedCliente);
            resp.sendRedirect(req.getContextPath() + "/Home");
        }else{
            req.setAttribute("errorMessage", "Formato non corretto o errore inserimento dati");
            req.getRequestDispatcher("/WEB-INF/jsp/error.jsp").forward(req, resp);
        }
    }
}
