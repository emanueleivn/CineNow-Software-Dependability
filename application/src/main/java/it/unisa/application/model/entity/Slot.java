package it.unisa.application.model.entity;

import java.sql.Time;

public class Slot {
    //@ spec_public
    private int id;
    //@ spec_public
    private Time oraInizio;

    /*@ public normal_behavior
      @   requires id >= 0 && oraInizio != null;
      @   assignable \nothing;
      @   ensures this.id == id;
      @   ensures this.oraInizio == oraInizio;
      @*/
    public Slot(int id, Time oraInizio) {
        this.id = id;
        this.oraInizio = oraInizio;
    }

    /*@ public normal_behavior
      @   ensures \result == oraInizio;
      @   assignable \nothing;
      @*/
    public Time getOraInizio() {
        return oraInizio;
    }

    /*@ public normal_behavior
      @   requires oraInizio != null;
      @   assignable this.oraInizio;
      @   ensures this.oraInizio == oraInizio;
      @*/
    public void setOraInizio(Time oraInizio) {
        this.oraInizio = oraInizio;
    }

    /*@ public normal_behavior
      @   ensures \result == id;
      @   assignable \nothing;
      @*/
    public int getId() {
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

    /*@ also public normal_behavior
      @   ensures \result != null;
      @   assignable \nothing;
      @*/
    @Override
    public String toString() {
        return "Slot{" +
                "id=" + id +
                ", oraInizio=" + oraInizio +
                '}';
    }
}
