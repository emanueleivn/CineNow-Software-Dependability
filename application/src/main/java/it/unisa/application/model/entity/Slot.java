package it.unisa.application.model.entity;

import java.sql.Time;

public class Slot {
    //@ spec_public
    private int id;
    //@ spec_public
    private Time oraInizio;

     public Slot(int id, Time oraInizio) {
        this.id = id;
        this.oraInizio = oraInizio;
    }

    //@ public normal_behavior
    //@ ensures \result == oraInizio;
    //@ assignable \nothing;
    /*@ pure @*/
    public Time getOraInizio() {
        return oraInizio;
    }

    //@ public normal_behavior
    //@ requires oraInizio != null;
    //@ ensures this.oraInizio != null;
    //@ assignable \everything;
    public void setOraInizio(Time oraInizio) {
        this.oraInizio = oraInizio;
    }

    //@ public normal_behavior
    //@ ensures \result == id;
    //@ assignable \nothing;
    /*@ pure @*/
    public int getId() {
        return id;
    }

    //@ public normal_behavior
    //@ requires id >= 0;
    //@ ensures this.id == id;
    //@ assignable \everything;
    public void setId(int id) {
        this.id = id;
    }

    //@ also public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    @Override
    public String toString() {
        return "Slot{" +
                "id=" + id +
                ", oraInizio=" + oraInizio +
                '}';
    }
}
