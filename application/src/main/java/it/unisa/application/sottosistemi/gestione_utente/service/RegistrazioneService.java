package it.unisa.application.sottosistemi.gestione_utente.service;

import it.unisa.application.model.dao.ClienteDAO;
import it.unisa.application.model.dao.UtenteDAO;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.utilities.*;

import java.util.HashMap;
import java.util.Map;

public class RegistrazioneService {
    private final ValidateStrategyManager validationManager;
    private final UtenteDAO utenteDAO;
    private final ClienteDAO clienteDAO;

    /**
     * Costruttore di default che inizializza i validatori.
     */

    public RegistrazioneService() {
        this.validationManager = new ValidateStrategyManager();
        this.utenteDAO = new UtenteDAO();
        this.clienteDAO = new ClienteDAO();

        validationManager.addValidator("email", new EmailValidator());
        validationManager.addValidator("password", new PasswordValidator());
        validationManager.addValidator("nome", new CampoValidator());
        validationManager.addValidator("cognome", new CampoValidator());
    }

    /**
     * Esegue la registrazione di un nuovo cliente.
     */

    public Cliente registrazione(String email, String password, String nome, String cognome) {
        Map<String, String> inputs = new HashMap<>();
        inputs.put("email", email);
        inputs.put("password", password);
        inputs.put("nome", nome);
        inputs.put("cognome", cognome);

        if (!validationManager.validate(inputs) || utenteDAO.retrieveByEmail(email) != null) {
            return null;
        }

        String passHash = PasswordHash.hash(password);
        Cliente cliente = new Cliente(email, passHash, nome, cognome);
        clienteDAO.create(cliente);
        return cliente;
    }
}
