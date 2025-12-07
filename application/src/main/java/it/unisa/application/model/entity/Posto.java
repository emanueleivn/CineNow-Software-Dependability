package it.unisa.application.model.entity;

public class Posto {
    //@ spec_public
    private Sala sala;
    //@ spec_public
    private char fila;
    //@ spec_public
    private int numero;

    public Posto(Sala sala, char fila, int numero) {
        this.sala = sala;
        this.fila = fila;
        this.numero = numero;
    }

    /*@ public normal_behavior
      @   ensures \result == sala;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Sala getSala() { return sala; }

    /*@ public normal_behavior
      @   requires sala != null;
      @   assignable this.sala;
      @   ensures this.sala == sala;
      @*/
    public void setSala(Sala sala) { this.sala = sala; }

    /*@ public normal_behavior
      @   ensures \result == fila;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ char getFila() { return fila; }

    /*@ public normal_behavior
      @   assignable this.fila;
      @   ensures this.fila == fila;
      @*/
    public void setFila(char fila) { this.fila = fila; }

    /*@ public normal_behavior
      @   ensures \result == numero;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getNumero() { return numero; }

    /*@ public normal_behavior
      @   requires numero > 0;
      @   assignable this.numero;
      @   ensures this.numero== numero;
      @*/
    public void setNumero(int numero) { this.numero = numero; }

    /*@ also public normal_behavior
      @   ensures \result != null;
      @   assignable \nothing;
      @*/
    @Override
    public String toString() {
        return "Posto{" +
                "sala=" + sala +
                ", fila=" + fila +
                ", numero=" + numero +
                '}';
    }
}
