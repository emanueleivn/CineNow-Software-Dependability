package it.unisa.application.sottosistemi.gestione_prenotazione.service;

import it.unisa.application.model.dao.PostoProiezioneDAO;
import it.unisa.application.model.dao.PrenotazioneDAO;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.model.entity.PostoProiezione;
import it.unisa.application.model.entity.Prenotazione;
import it.unisa.application.model.entity.Proiezione;

import java.util.List;

public class PrenotazioneService {

    //@ spec_public
    private final PrenotazioneDAO prenotazioneDAO = new PrenotazioneDAO();
    //@ spec_public
    private final PostoProiezioneDAO postoProiezioneDAO = new PostoProiezioneDAO();

    //@ public invariant prenotazioneDAO != null && postoProiezioneDAO != null;

    /**
     * Costruttore di default.
     */
    /*@ public behavior
      @   ensures prenotazioneDAO != null && postoProiezioneDAO != null;
      @*/
    public PrenotazioneService() {}

    /**
     * Crea una nuova prenotazione occupando i posti selezionati.
     */
    /*@ public behavior
      @   requires cliente != null;
      @   requires proiezione != null;
      @   requires posti != null;
      @   requires posti.size() > 0;
      @   requires (\forall int i; 0 <= i && i < posti.size();
      @                posti.get(i) != null);
      @
      @   // Usa DAO e DB: modelliamo in modo conservativo
      @   assignable \everything;
      @
      @   // Non imponiamo che non vengano lanciate eccezioni:
      @   // il metodo può terminare sia normalmente sia con eccezioni runtime.
      @*/
    public void aggiungiOrdine(Cliente cliente, List<PostoProiezione> posti, Proiezione proiezione) {
        if (cliente == null || posti == null || posti.isEmpty() || proiezione == null) {
            throw new IllegalArgumentException("Cliente, posti e proiezione non possono essere null.");
        }
        for (PostoProiezione postoProiezione : posti) {
            if (!postoProiezione.isStato()) {
                throw new IllegalArgumentException("Posti occupati");
            }
        }

        Prenotazione prenotazione = new Prenotazione(0, cliente, proiezione);

        if (!prenotazioneDAO.create(prenotazione)) {
            throw new RuntimeException("Errore durante la creazione della prenotazione.");
        }

        for (PostoProiezione postoProiezione : posti) {
            if (!postoProiezioneDAO.occupaPosto(postoProiezione, prenotazione.getId())) {
                throw new RuntimeException("Errore durante l'occupazione del posto.");
            }
        }

    }

    /**
     * Restituisce i posti associati alla proiezione.
     */
    /*@ public behavior
      @   requires proiezione != null;
      @   assignable \everything;
      @   ensures \result != null;
      @*/
    public List<PostoProiezione> ottieniPostiProiezione(Proiezione proiezione){
        return postoProiezioneDAO.retrieveAllByProiezione(proiezione);
    }
}
