package it.unisa.application.sottosistemi.gestione_utente.service;

import it.unisa.application.model.dao.ClienteDAO;
import it.unisa.application.model.dao.SedeDAO;
import it.unisa.application.model.dao.UtenteDAO;
import it.unisa.application.model.entity.GestoreSede;
import it.unisa.application.model.entity.Sede;
import it.unisa.application.model.entity.Utente;
import it.unisa.application.utilities.PasswordHash;
import jakarta.servlet.http.HttpSession;

import java.security.MessageDigest;


public class AutenticazioneService {

    private final UtenteDAO utenteDAO;
    private final ClienteDAO clienteDAO;

    public AutenticazioneService() {
        this.utenteDAO = new UtenteDAO();
        this.clienteDAO = new ClienteDAO();
    }

    /**
     * Confronto constant-time per prevenire timing attacks
     */
    private boolean constantTimeEquals(String a, String b) {
        if (a == null || b == null) {
            return (a == null && b == null);
        }
        if (a.length() != b.length()) {
            return false;
        }
        return MessageDigest.isEqual(a.getBytes(), b.getBytes());
    }

    public Utente login(String email, String password) {
        Utente baseUser = utenteDAO.retrieveByEmail(email);
        if (baseUser == null) {
            return null;
        }
        String passHash = PasswordHash.hash(password);
        // Usa confronto constant-time per prevenire timing attacks
        if (!constantTimeEquals(baseUser.getPassword(), passHash)) {
            return null;
        }
        if (baseUser.getRuolo().equalsIgnoreCase("cliente")) {
            return clienteDAO.retrieveByEmail(email, passHash);
        }
        if (baseUser.getRuolo().equalsIgnoreCase("gestore_sede")) {
            SedeDAO sedeDAO = new SedeDAO();
            Sede sede = sedeDAO.retrieveByGestoreEmail(baseUser.getEmail());
            GestoreSede gs = new GestoreSede(baseUser.getEmail(), baseUser.getPassword(),sede);
            gs.setRuolo(baseUser.getRuolo());
            return gs;
        }
        return baseUser;
    }

    public void logout(HttpSession session) {
        session.invalidate();
    }
}
