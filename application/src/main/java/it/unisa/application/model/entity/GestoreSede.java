package it.unisa.application.model.entity;

public class GestoreSede extends Utente {
    //@ spec_public
    private Sede sede;

    /*@ public normal_behavior
      @   requires email != null && password != null && sede != null;
      @   assignable \everything;
      @   ensures this.sede == sede;
      @*/
    public GestoreSede(String email, String password, Sede sede) {
        super(email, password, "gestore_sede");
        this.sede = sede;
    }

    /*@ public normal_behavior
      @   ensures \result == sede;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Sede getSede() { return sede; }

    /*@ public normal_behavior
      @   requires sede != null;
      @   assignable this.sede;
      @   ensures this.sede == sede;
      @*/
    public void setSede(Sede sede) { this.sede = sede; }

    //@ also public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    @Override
    public String toString() {
        return "GestoreSede{" +
                "sede=" + sede +
                '}';
    }
}
