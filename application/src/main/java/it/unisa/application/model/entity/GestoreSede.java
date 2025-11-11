package it.unisa.application.model.entity;

public class GestoreSede extends Utente {
    //@ public invariant sede != null;

    //@ spec_public
    private Sede sede;

    //@ public normal_behavior
    //@ requires email != null && password != null && sede != null;
    //@ ensures this.sede == sede;
    //@ assignable \everything;
    public GestoreSede(/*@ non_null @*/ String email, /*@ non_null @*/ String password,
                       /*@ non_null @*/ Sede sede) {
        super(email, password, "gestore_sede"); // super per primo
        /*@ assert sede != null; @*/
        this.sede = sede;
    }

    //@ public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    public Sede getSede() { return sede; }

    //@ public normal_behavior
    //@ requires sede != null;
    //@ ensures this.sede != null;
    //@ assignable \everything;
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
