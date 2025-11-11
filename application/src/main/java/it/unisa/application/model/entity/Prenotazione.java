package it.unisa.application.model.entity;

import java.util.List;

public class Prenotazione {
    //@ public invariant id >= 0;
    //@ public invariant proiezione != null;
    //@ public invariant cliente != null;

    //@ spec_public
    private int id;
    //@ spec_public
    private Proiezione proiezione;
    //@ spec_public
    /*@ nullable @*/
    private List<PostoProiezione> postiPrenotazione;
    //@ spec_public
    private Cliente cliente;

    //@ public normal_behavior
    //@ requires id >= 0 && cliente != null && proiezione != null;
    //@ ensures this.id >= 0 && this.cliente != null && this.proiezione != null;
    //@ assignable \everything;
    public Prenotazione(int id, Cliente cliente, Proiezione proiezione) {
        this.id = id;
        this.cliente = cliente;
        this.proiezione = proiezione;
        this.postiPrenotazione = null;
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
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    public Proiezione getProiezione() { return proiezione; }

    //@ public normal_behavior
    //@ requires proiezione != null;
    //@ ensures this.proiezione != null;
    //@ assignable \everything;
    public void setProiezione(Proiezione proiezione) { this.proiezione = proiezione; }

    //@ public normal_behavior
    //@ assignable \nothing;
    /*@ pure @*/
    /*@ nullable @*/
    public List<PostoProiezione> getPostiPrenotazione() { return postiPrenotazione; }

    //@ public normal_behavior
    //@ requires postiProiezione != null;
    //@ ensures this.postiPrenotazione != null;
    //@ assignable \everything;
    public void setPostiPrenotazione(List<PostoProiezione> postiProiezione) { this.postiPrenotazione = postiProiezione; }

    //@ public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    public Cliente getCliente() { return cliente; }

    //@ public normal_behavior
    //@ requires cliente != null;
    //@ ensures this.cliente != null;
    //@ assignable \everything;
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
