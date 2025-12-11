package it.unisa.application.model.entity;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

public class Sala {
    //@ spec_public
    private int id;
    //@ spec_public
    private int numeroSala;
    //@ spec_public
    private int capienza;
    //@ spec_public
    private List<Slot> slotList;
    //@ spec_public
    private List<Proiezione> proiezioni;
    //@ spec_public
    private List<Posto> posti;
    //@ spec_public
    private Sede sede;

    //@ public invariant id >= 0;
    //@ public invariant numeroSala > 0;
    //@ public invariant capienza > 0;
    //@ public invariant slotList != null && proiezioni != null && posti != null;
    //@ public invariant sede != null;

    /*@ public normal_behavior
      @   requires id >= 0;
      @   requires numeroSala > 0;
      @   requires capienza > 0;
      @   requires sede != null;
      @   assignable \nothing;
      @   ensures this.id == id;
      @   ensures this.numeroSala == numeroSala;
      @   ensures this.capienza == capienza;
      @   ensures this.sede == sede;
      @   ensures this.slotList != null && this.proiezioni != null && this.posti != null;
      @*/
    public Sala(int id, int numeroSala, int capienza, Sede sede) {
        this.id = id;
        this.numeroSala = numeroSala;
        this.capienza = capienza;
        this.sede = sede;
        this.slotList = new ArrayList<Slot>();
        this.proiezioni = new ArrayList<Proiezione>();
        this.posti = new ArrayList<Posto>();
    }

    /*@ public normal_behavior
      @   ensures \result == id;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getId() {
        return id;
    }

    /*@ public normal_behavior
      @   requires id >= 0;
      @   assignable this.id;
      @   ensures this.id == id;
      @*/
    public void setId(int id) {
        this.id = id;
    }

    /*@ public normal_behavior
      @   ensures \result == numeroSala;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getNumeroSala() {
        return numeroSala;
    }

    /*@ public normal_behavior
      @   requires numeroSala > 0;
      @   assignable this.numeroSala;
      @   ensures this.numeroSala == numeroSala;
      @*/
    public void setNumeroSala(int numeroSala) {
        this.numeroSala = numeroSala;
    }

    /*@ public normal_behavior
      @   ensures \result == capienza;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getCapienza() {
        return capienza;
    }

    /*@ public normal_behavior
      @   requires capienza > 0;
      @   assignable this.capienza;
      @   ensures this.capienza == capienza;
      @*/
    public void setCapienza(int capienza) {
        this.capienza = capienza;
    }

    /*@ public normal_behavior
      @   ensures \result == sede;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Sede getSede() {
        return sede;
    }

    /*@ public normal_behavior
      @   requires sede != null;
      @   assignable this.sede;
      @   ensures this.sede == sede;
      @*/
    public void setSede(Sede sede) {
        this.sede = sede;
    }

    /*@ public normal_behavior
      @   ensures \result == slotList;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ List<Slot> slotList() {
        return slotList;
    }

    /*@ public normal_behavior
      @   requires slotList != null;
      @   assignable this.slotList;
      @   ensures this.slotList == slotList;
      @*/
    public void setSlotList(List<Slot> slotList) {
        this.slotList = slotList;
    }

    /*@ public normal_behavior
      @   ensures \result == proiezioni;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ List<Proiezione> getProiezioni() {
        return proiezioni;
    }

    /*@ public normal_behavior
      @   requires proiezioni != null;
      @   assignable this.proiezioni;
      @   ensures this.proiezioni == proiezioni;
      @*/
    public void setProiezioni(List<Proiezione> proiezioni) {
        this.proiezioni = proiezioni;
    }

    /*@ public normal_behavior
      @   ensures \result == posti;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ List<Posto> getPosti() {
        return posti;
    }

    /*@ public normal_behavior
      @   requires posti != null;
      @   assignable this.posti;
      @   ensures this.posti == posti;
      @*/
    public void setPosti(List<Posto> posti) {
        this.posti = posti;
    }

    /*@ public normal_behavior
      @   ensures \result == slotList;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ List<Slot> getSlotList() {
        return slotList;
    }

    /*@ public normal_behavior
      @   requires id >= 0;
      @   requires slot != null && data != null && film != null;
      @   requires film.getId() >= 0;
      @   requires film.getTitolo() != null;
      @   requires film.getGenere() != null;
      @   requires film.getClassificazione() != null;
      @   requires film.getDurata() > 0;
      @   requires film.getLocandina() != null;
      @   requires film.getDescrizione() != null;
      @   requires this.proiezioni != null;
      @   assignable this.proiezioni, this.proiezioni.values;
      @   ensures this.proiezioni.size() == \old(this.proiezioni).size() + 1;
      @   ensures \result == this.proiezioni;
      @*/
    //@ skipesc
    public List<Proiezione> aggiungiProiezione(int id, Slot slot, LocalDate data, Film film) {
        Proiezione proiezione = new Proiezione(id, this, film, data, slot);
        proiezione.setPostiProiezione(creaListaPosti(proiezione));
        this.proiezioni.add(proiezione);
        return proiezioni;
    }


    /*@ private normal_behavior
      @   requires proiezione != null;
      @   requires this.posti != null;
      @   ensures \result != null;
      @   ensures \result.size() == this.posti.size();
      @   assignable \nothing;
      @*/
    //@ skipesc
    private List<PostoProiezione> creaListaPosti(Proiezione proiezione) {
        ArrayList<PostoProiezione> postiList = new ArrayList<PostoProiezione>();
        // Salvo la size per evitare chiamate ripetute nel loop (O(n) -> O(1))
        int postiCount = this.posti.size();
        for (int i = 0; i < postiCount; ++i) {
            Posto p = this.posti.get(i);
            postiList.add(new PostoProiezione(p, proiezione));
        }
        return postiList;
    }

    //@ also public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    @Override
    public String toString() {
        return "Sala{" +
                "id=" + id +
                ", numeroSala=" + numeroSala +
                ", capienza=" + capienza +
                ", slotList=" + slotList +
                ", proiezioni=" + proiezioni +
                ", posti=" + posti +
                '}';
    }
}
