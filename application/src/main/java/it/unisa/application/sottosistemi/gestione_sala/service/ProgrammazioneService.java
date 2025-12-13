package it.unisa.application.sottosistemi.gestione_sala.service;

import it.unisa.application.model.dao.FilmDAO;
import it.unisa.application.model.dao.ProiezioneDAO;
import it.unisa.application.model.dao.SalaDAO;
import it.unisa.application.model.dao.SlotDAO;
import it.unisa.application.model.entity.Film;
import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.model.entity.Sala;
import it.unisa.application.model.entity.Slot;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

public class ProgrammazioneService {
    private final FilmDAO filmDAO;
    private final SalaDAO salaDAO;
    private final SlotDAO slotDAO;
    private final ProiezioneDAO proiezioneDAO;

    public ProgrammazioneService() {
        this.filmDAO = new FilmDAO();
        this.salaDAO = new SalaDAO();
        this.slotDAO = new SlotDAO();
        this.proiezioneDAO = new ProiezioneDAO();
    }

    // Costruttore protetto per permettere l'iniezione dei DAO nei test
    protected ProgrammazioneService(FilmDAO filmDAO, SalaDAO salaDAO, SlotDAO slotDAO, ProiezioneDAO proiezioneDAO) {
        this.filmDAO = filmDAO;
        this.salaDAO = salaDAO;
        this.slotDAO = slotDAO;
        this.proiezioneDAO = proiezioneDAO;
    }

    /**
     * Aggiunge una nuova proiezione in sala per la data indicata.
     */

    public boolean aggiungiProiezione(int filmId, int salaId, List<Integer> slotIds, LocalDate data) {
        try {
            Film film = filmDAO.retrieveById(filmId);
            Sala sala = salaDAO.retrieveById(salaId);

            if (film == null) {
                throw new RuntimeException("Film non trovato.");
            }
            if (sala == null) {
                throw new RuntimeException("Sala non trovata.");
            }
            if (data.isBefore(LocalDate.now())) {
                throw new RuntimeException("Errore data.");
            }

            List<Slot> slotsDisponibili = slotDAO.retrieveAllSlots();

            // Filtro manuale degli slot selezionati (senza stream)
            List<Slot> slotsSelezionati = new ArrayList<>();
            // Salvo la size per evitare chiamate ripetute nel loop (O(n) -> O(1))
            int slotsDisponibiliCount = slotsDisponibili.size();
            for (int i = 0; i < slotsDisponibiliCount; ++i) {
                Slot slot = slotsDisponibili.get(i);
                if (slotIds.contains(slot.getId())) {
                    slotsSelezionati.add(slot);
                }
            }

            // Ordinamento per ora di inizio (senza lambda/anonime)
            sortSlotsByOraInizio(slotsSelezionati);

            if (slotsSelezionati.isEmpty()) {
                throw new RuntimeException("Nessuno slot valido selezionato.");
            }

            Slot primoSlot = slotsSelezionati.get(0);

            Proiezione proiezione = new Proiezione(0, sala, film, data, primoSlot);
            return this.proiezioneDAO.create(proiezione);
        } catch (Exception e) {
            return false;
        }
    }

    private static void sortSlotsByOraInizio(List<Slot> slots) {
        int slotsSize = slots.size();
        for (int i = 1; i < slotsSize; ++i) {
            Slot key = slots.get(i);
            int j = i - 1;
            while (j >= 0 && slots.get(j).getOraInizio().compareTo(key.getOraInizio()) > 0) {
                slots.set(j + 1, slots.get(j));
                j--;
            }
            slots.set(j + 1, key);
        }
    }
}
