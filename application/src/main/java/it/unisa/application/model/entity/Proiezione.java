package it.unisa.application.model.entity;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

public class Proiezione {
    //@ public invariant id >= 0;
    //@ public invariant postiProiezione != null;

    //@ spec_public
    private int id;
    //@ spec_public
    /*@ nullable @*/
    private Film filmProiezione;
    //@ spec_public
    /*@ nullable @*/
    private Sala salaProiezione;
    //@ spec_public
    /*@ nullable @*/
    private LocalDate dataProiezione;
    //@ spec_public
    private List<PostoProiezione> postiProiezione;
    //@ spec_public
    /*@ nullable @*/
    private Slot orarioProiezione;

    //@ public normal_behavior
    //@ requires id >= 0 && salaProiezione != null && filmProiezione != null && dataProiezione != null && orarioProiezione != null;
    //@ ensures this.id >= 0 && this.salaProiezione != null && this.postiProiezione != null;
    //@ assignable \everything;
    public Proiezione(int id, Sala salaProiezione, Film filmProiezione, LocalDate dataProiezione, Slot orarioProiezione) {
        /*@
          assert id >= 0 && salaProiezione != null && filmProiezione != null && dataProiezione != null && orarioProiezione != null;
        @*/
        this.id = id;
        this.salaProiezione = salaProiezione;
        this.filmProiezione = filmProiezione;
        this.dataProiezione = dataProiezione;
        this.orarioProiezione = orarioProiezione;
        postiProiezione = new ArrayList<>();
        /*@
          assert this.id >= 0 && this.salaProiezione != null && this.postiProiezione != null;
        @*/
    }

    //@ public normal_behavior
    //@ requires id >= 0 && salaProiezione != null && filmProiezione != null && dataProiezione != null && postiProiezione != null && orarioProiezione != null;
    //@ ensures this.id >= 0 && this.salaProiezione != null && this.postiProiezione != null;
    //@ assignable \everything;
    public Proiezione(int id, Sala salaProiezione, Film filmProiezione, LocalDate dataProiezione, List<PostoProiezione> postiProiezione, Slot orarioProiezione) {
        /*@
          assert id >= 0 && salaProiezione != null && filmProiezione != null && dataProiezione != null && postiProiezione != null && orarioProiezione != null;
        @*/
        this.id = id;
        this.salaProiezione = salaProiezione;
        this.filmProiezione = filmProiezione;
        this.dataProiezione = dataProiezione;
        this.postiProiezione = postiProiezione;
        this.orarioProiezione = orarioProiezione;
        /*@
          assert this.id >= 0 && this.salaProiezione != null && this.postiProiezione != null;
        @*/
    }

    //@ public normal_behavior
    //@ requires id >= 0;
    //@ ensures this.id >= 0 && this.postiProiezione != null;
    //@ assignable \everything;
    public Proiezione(int id) {
        this.id = id;
        this.postiProiezione = new ArrayList<>();
    }

    //@ public normal_behavior
    //@ ensures \result >= 0;
    //@ assignable \nothing;
    /*@ pure @*/
    public int getId() { return id; }

    //@ public normal_behavior
    //@ requires id >= 0;
    //@ ensures this.id >= 0;
    //@ assignable \everything;
    public void setId(int id) { this.id = id; }

    //@ public normal_behavior
    //@ ensures \result == this.filmProiezione;
    //@ assignable \nothing;
    /*@ pure @*/
    /*@ nullable @*/
    public Film getFilmProiezione() { return filmProiezione; }

    //@ public normal_behavior
    //@ requires filmProiezione != null;
    //@ ensures this.filmProiezione != null;
    //@ assignable \everything;
    public void setFilmProiezione(Film filmProiezione) { this.filmProiezione = filmProiezione; }

    //@ public normal_behavior
    //@ ensures \result == this.salaProiezione;
    //@ assignable \nothing;
    /*@ pure @*/
    /*@ nullable @*/
    public Sala getSalaProiezione() { return salaProiezione; }

    //@ public normal_behavior
    //@ requires salaProiezione != null;
    //@ ensures this.salaProiezione != null;
    //@ assignable \everything;
    public void setSalaProiezione(Sala salaProiezione) { this.salaProiezione = salaProiezione; }

    //@ public normal_behavior
    //@ ensures \result == this.dataProiezione;
    //@ assignable \nothing;
    /*@ pure @*/
    /*@ nullable @*/
    public LocalDate getDataProiezione() { return dataProiezione; }

    //@ public normal_behavior
    //@ requires dataProiezione != null;
    //@ ensures this.dataProiezione != null;
    //@ assignable \everything;
    public void setDataProiezione(LocalDate dataProiezione) { this.dataProiezione = dataProiezione; }

    //@ public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    public List<PostoProiezione> getPostiProiezione() { return postiProiezione; }

    //@ public normal_behavior
    //@ requires postiProiezione != null;
    //@ ensures this.postiProiezione != null;
    //@ assignable \everything;
    public void setPostiProiezione(List<PostoProiezione> postiProiezione) { this.postiProiezione = postiProiezione; }

    //@ public normal_behavior
    //@ ensures \result == this.orarioProiezione;
    //@ assignable \nothing;
    /*@ pure @*/
    /*@ nullable @*/
    public Slot getOrarioProiezione() { return orarioProiezione; }

    //@ public normal_behavior
    //@ requires orarioProiezione != null;
    //@ ensures this.orarioProiezione != null;
    //@ assignable \everything;
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
