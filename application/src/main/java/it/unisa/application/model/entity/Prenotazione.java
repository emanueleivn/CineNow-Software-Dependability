package it.unisa.application.model.entity;

import java.util.List;

public class Prenotazione {
    //@ spec_public
    private int id;
    //@ spec_public
    private Proiezione proiezione;
    //@ spec_public
    /*@ nullable @*/
    private List<PostoProiezione> postiPrenotazione;
    //@ spec_public
    private Cliente cliente;

    /*@ public normal_behavior
      @   requires id >= 0 && cliente != null && proiezione != null;
      @   assignable \everything;
      @   ensures this.id == id;
      @   ensures this.cliente == cliente;
      @   ensures this.proiezione == proiezione;
      @   ensures this.postiPrenotazione == null;
      @*/
    public Prenotazione(int id, Cliente cliente, Proiezione proiezione) {
        this.id = id;
        this.cliente = cliente;
        this.proiezione = proiezione;
        this.postiPrenotazione = null;
    }

    /*@ public normal_behavior
      @   ensures \result == id;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getId() { return id; }

    /*@ public normal_behavior
     @   assignable this.id;
     @   ensures this.id == id;
     @*/
    public void setId(int id) { this.id = id; }

    /*@ public normal_behavior
      @   ensures \result == proiezione;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Proiezione getProiezione() { return proiezione; }

    /*@ public normal_behavior
      @   requires proiezione != null;
      @   assignable this.proiezione;
      @   ensures this.proiezione == proiezione;
      @*/
    public void setProiezione(Proiezione proiezione) { this.proiezione = proiezione; }

    /*@ public normal_behavior
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ /*@ nullable @*/ List<PostoProiezione> getPostiPrenotazione() { return postiPrenotazione; }

    /*@ public normal_behavior
      @   requires postiProiezione != null;
      @   assignable this.postiPrenotazione;
      @   ensures this.postiPrenotazione == postiProiezione;
      @*/
    public void setPostiPrenotazione(List<PostoProiezione> postiProiezione) { this.postiPrenotazione = postiProiezione; }

    /*@ public normal_behavior
      @   ensures \result == cliente;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Cliente getCliente() { return cliente; }

    /*@ public normal_behavior
      @   requires cliente != null;
      @   assignable this.cliente;
      @   ensures this.cliente == cliente;
      @*/
    public void setCliente(Cliente cliente) { this.cliente = cliente; }

    //@ also public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    @Override
    public String toString() {
        return "Prenotazione{" +
                "id=" + id +
                ", proiezione=" + proiezione +
                ", postiPrenotazione=" + postiPrenotazione +
                ", cliente=" + cliente +
                '}';
    }
}
