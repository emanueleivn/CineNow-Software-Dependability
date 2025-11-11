package it.unisa.application.model.entity;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

public class Sala {
    //@ public invariant id >= 0;
    //@ public invariant numeroSala > 0;
    //@ public invariant capienza > 0;
    //@ public invariant slotList != null;
    //@ public invariant proiezioni != null;
    //@ public invariant posti != null;
    //@ public invariant sede != null;

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

    //@ public normal_behavior
    //@ requires id >= 0 && numeroSala > 0 && capienza > 0 && sede != null;
    //@ ensures this.id >= 0 && this.numeroSala > 0 && this.capienza > 0 && this.sede != null;
    //@ assignable \everything;
    public Sala(int id, int numeroSala, int capienza, Sede sede) {
        this.id = id;
        this.numeroSala = numeroSala;
        this.capienza = capienza;
        this.sede = sede;
        this.slotList = new ArrayList<>();
        this.proiezioni = new ArrayList<>();
        this.posti = new ArrayList<>();
    }

    //@ public normal_behavior
    //@ ensures \result >= 0;
    //@ assignable \nothing;
    /*@ pure @*/
    public int getId() {
        return id;
    }

    //@ public normal_behavior
    //@ requires id >= 0;
    //@ ensures this.id >= 0;
    //@ assignable \everything;
    public void setId(int id) {
        this.id = id;
    }

    //@ public normal_behavior
    //@ ensures \result > 0;
    //@ assignable \nothing;
    /*@ pure @*/
    public int getNumeroSala() {
        return numeroSala;
    }

    //@ public normal_behavior
    //@ requires numeroSala > 0;
    //@ ensures this.numeroSala > 0;
    //@ assignable \everything;
    public void setNumeroSala(int numeroSala) {
        this.numeroSala = numeroSala;
    }

    //@ public normal_behavior
    //@ ensures \result > 0;
    //@ assignable \nothing;
    /*@ pure @*/
    public int getCapienza() {
        return capienza;
    }

    //@ public normal_behavior
    //@ requires capienza > 0;
    //@ ensures this.capienza > 0;
    //@ assignable \everything;
    public void setCapienza(int capienza) {
        this.capienza = capienza;
    }

    //@ public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    public Sede getSede() {
        return sede;
    }

    //@ public normal_behavior
    //@ requires sede != null;
    //@ ensures this.sede != null;
    //@ assignable \everything;
    public void setSede(Sede sede) {
        this.sede = sede;
    }

    //@ public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    public List<Slot> slotList() {
        return slotList;
    }

    //@ public normal_behavior
    //@ requires slotList != null;
    //@ ensures this.slotList != null;
    //@ assignable \everything;
    public void setSlotList(List<Slot> slotList) {
        this.slotList = slotList;
    }

    //@ public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    public List<Proiezione> getProiezioni() {
        return proiezioni;
    }

    //@ public normal_behavior
    //@ requires proiezioni != null;
    //@ ensures this.proiezioni != null;
    //@ assignable \everything;
    public void setProiezioni(List<Proiezione> proiezioni) {
        this.proiezioni = proiezioni;
    }

    //@ public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    public List<Posto> getPosti() {
        return posti;
    }

    //@ public normal_behavior
    //@ requires posti != null;
    //@ ensures this.posti != null;
    //@ assignable \everything;
    public void setPosti(List<Posto> posti) {
        this.posti = posti;
    }

    //@ public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    public List<Slot> getSlotList() {
        return slotList;
    }

    //@ public normal_behavior
    //@ requires slot != null && data != null && film != null;
    //@ requires this.proiezioni != null && this.posti != null && this.slotList != null && this.sede != null;
    //@ ensures this.proiezioni != null && this.proiezioni.size() == \old(this.proiezioni.size()) + 1;
    //@ ensures this.id == \old(this.id) && this.numeroSala == \old(this.numeroSala) && this.capienza == \old(this.capienza);
    //@ ensures this.slotList == \old(this.slotList) && this.posti == \old(this.posti) && this.sede == \old(this.sede);
    //@ assignable this.proiezioni;
    public List<Proiezione> aggiungiProiezione(int id, Slot slot, LocalDate data, Film film) {
        /*@ assert slot != null && data != null && film != null; @*/
        Proiezione proiezione = new Proiezione(id, this, film, data, slot);
        /*@ assert proiezione != null; @*/
        proiezione.setPostiProiezione(creaListaPosti(proiezione));
        this.proiezioni.add(proiezione);
        return proiezioni;
    }

    //@ private normal_behavior
    //@ requires proiezione != null && this.posti != null && this.proiezioni != null && this.slotList != null && this.sede != null;
    //@ ensures \result != null;
    //@ ensures this.id == \old(this.id) && this.numeroSala == \old(this.numeroSala) && this.capienza == \old(this.capienza);
    //@ ensures this.slotList == \old(this.slotList) && this.proiezioni == \old(this.proiezioni) && this.posti == \old(this.posti) && this.sede == \old(this.sede);
    //@ assignable \everything;
    private List<PostoProiezione> creaListaPosti(Proiezione proiezione) {
        ArrayList<PostoProiezione> postiList = new ArrayList<>();
        //@ loop_invariant 0 <= postiList.size();
        //@ decreases posti.size() - postiList.size();
        for (Posto p : this.posti) {
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
