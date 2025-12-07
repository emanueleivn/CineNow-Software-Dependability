package it.unisa.application.model.entity;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

public class Proiezione {
    //@ spec_public
    private int id;
    //@ spec_public
    private Film filmProiezione;
    //@ spec_public
    private Sala salaProiezione;
    //@ spec_public
    private LocalDate dataProiezione;
    //@ spec_public
    private List<PostoProiezione> postiProiezione;
    //@ spec_public
    private Slot orarioProiezione;

    /*@ public normal_behavior
      @   requires salaProiezione != null && filmProiezione != null && dataProiezione != null && orarioProiezione != null;
      @   requires id >= 0;
      @   assignable \everything;
      @   ensures this.id == id;
      @   ensures this.salaProiezione == salaProiezione;
      @   ensures this.filmProiezione == filmProiezione;
      @   ensures this.dataProiezione == dataProiezione;
      @   ensures this.orarioProiezione == orarioProiezione;
      @   ensures this.postiProiezione != null;
      @*/
    public Proiezione(int id, Sala salaProiezione, Film filmProiezione,
                      LocalDate dataProiezione, Slot orarioProiezione) {
        this.id = id;
        this.salaProiezione = salaProiezione;
        this.filmProiezione = filmProiezione;
        this.dataProiezione = dataProiezione;
        this.orarioProiezione = orarioProiezione;
        this.postiProiezione = new ArrayList<>();
    }

    /*@ public normal_behavior
      @   requires salaProiezione != null && filmProiezione != null && dataProiezione != null && orarioProiezione != null && postiProiezione != null;
      @   requires id >= 0;
      @   assignable \everything;
      @   ensures this.id == id;
      @   ensures this.salaProiezione == salaProiezione;
      @   ensures this.filmProiezione == filmProiezione;
      @   ensures this.dataProiezione == dataProiezione;
      @   ensures this.orarioProiezione == orarioProiezione;
      @   ensures this.postiProiezione == postiProiezione;
      @*/
    public Proiezione(int id, Sala salaProiezione, Film filmProiezione,
                      LocalDate dataProiezione, List<PostoProiezione> postiProiezione,
                      Slot orarioProiezione) {
        this.id = id;
        this.salaProiezione = salaProiezione;
        this.filmProiezione = filmProiezione;
        this.dataProiezione = dataProiezione;
        this.postiProiezione = postiProiezione;
        this.orarioProiezione = orarioProiezione;
    }

    /*@ public normal_behavior
      @   requires id >= 0;
      @   assignable \everything;
      @   ensures this.id == id;
      @   ensures this.postiProiezione != null;
      @*/
    public Proiezione(int id) {
        this.id = id;
        this.postiProiezione = new ArrayList<>();
    }

    /*@ public normal_behavior
      @   ensures \result == id;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getId() { return id; }

    /*@ public normal_behavior
      @   requires id >= 0;
      @   assignable this.id;
      @   ensures this.id == id;
      @*/
    public void setId(int id) { this.id = id; }

    /*@ public normal_behavior
      @   ensures \result == this.filmProiezione;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Film getFilmProiezione() { return filmProiezione; }

    /*@ public normal_behavior
      @   requires filmProiezione != null;
      @   assignable this.filmProiezione;
      @   ensures this.filmProiezione == filmProiezione;
      @*/
    public void setFilmProiezione(Film filmProiezione) { this.filmProiezione = filmProiezione; }

    /*@ public normal_behavior
      @   ensures \result == this.salaProiezione;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Sala getSalaProiezione() { return salaProiezione; }

    /*@ public normal_behavior
      @   requires salaProiezione != null;
      @   assignable this.salaProiezione;
      @   ensures this.salaProiezione == salaProiezione;
      @*/
    public void setSalaProiezione(Sala salaProiezione) { this.salaProiezione = salaProiezione; }

    /*@ public normal_behavior
      @   ensures \result == this.dataProiezione;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ LocalDate getDataProiezione() { return dataProiezione; }

    /*@ public normal_behavior
      @   requires dataProiezione != null;
      @   assignable this.dataProiezione;
      @   ensures this.dataProiezione == dataProiezione;
      @*/
    public void setDataProiezione(LocalDate dataProiezione) { this.dataProiezione = dataProiezione; }

    /*@ public normal_behavior
      @   ensures \result == this.postiProiezione;
      @   ensures \result != null;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ List<PostoProiezione> getPostiProiezione() { return postiProiezione; }

    /*@ public normal_behavior
      @   requires postiProiezione != null;
      @   assignable this.postiProiezione;
      @   ensures this.postiProiezione == postiProiezione;
      @*/
    public void setPostiProiezione(List<PostoProiezione> postiProiezione) { this.postiProiezione = postiProiezione; }

    /*@ public normal_behavior
      @   ensures \result == this.orarioProiezione;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Slot getOrarioProiezione() { return orarioProiezione; }

    /*@ public normal_behavior
      @   requires orarioProiezione != null;
      @   assignable this.orarioProiezione;
      @   ensures this.orarioProiezione == orarioProiezione;
      @*/
    public void setOrarioProiezione(Slot orarioProiezione) { this.orarioProiezione = orarioProiezione; }

    //@ also public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    @Override
    public String toString() {
        return "Proiezione{" +
                "id=" + id +
                ", filmProiezione=" + filmProiezione +
                ", salaProiezione=" + salaProiezione +
                ", dataProiezione=" + dataProiezione +
                ", postiProiezione=" + postiProiezione +
                ", orarioProiezione=" + orarioProiezione +
                '}';
    }
}
