package it.unisa.application.model.entity;

public class Posto {
    //@ public invariant sala != null;
    //@ public invariant numero > 0;

    //@ spec_public
    private Sala sala;
    //@ spec_public
    private char fila;
    //@ spec_public
    private int numero;

    //@ public normal_behavior
    //@ requires sala != null && numero > 0;
    //@ ensures this.sala == sala && this.fila == fila && this.numero == numero;
    //@ assignable \everything;
    public Posto(Sala sala, char fila, int numero) {
        this.sala = sala;
        this.fila = fila;
        this.numero = numero;
    }

    //@ public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    public Sala getSala() { return sala; }

    //@ public normal_behavior
    //@ requires sala != null;
    //@ ensures this.sala != null;
    //@ assignable \everything;
    public void setSala(Sala sala) { this.sala = sala; }

    //@ public normal_behavior
    //@ assignable \nothing;
    /*@ pure @*/
    public char getFila() { return fila; }

    //@ public normal_behavior
    //@ assignable \everything;
    public void setFila(char fila) { this.fila = fila; }

    //@ public normal_behavior
    //@ ensures \result > 0;
    //@ assignable \nothing;
    /*@ pure @*/
    public int getNumero() { return numero; }

    //@ public normal_behavior
    //@ requires numero > 0;
    //@ ensures this.numero > 0;
    //@ assignable \everything;
    public void setNumero(int numero) { this.numero = numero; }

    //@ also public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    @Override
    public String toString() {
        return "Posto{" +
                "sala=" + sala +
                ", fila=" + fila +
                ", numero=" + numero +
                '}';
    }
}
