package it.unisa.application.model.entity;

import java.util.ArrayList;
import java.util.List;

public class Cliente extends Utente {
    //@ public invariant prenotazioni != null;

    //@ spec_public
    /*@ nullable @*/
    private String nome;
    //@ spec_public
    /*@ nullable @*/
    private String cognome;
    //@ spec_public
    private List<Prenotazione> prenotazioni;

    //@ public normal_behavior
    //@ requires email != null && password != null && nome != null && cognome != null;
    //@ ensures this.prenotazioni != null && this.getNome() == nome && this.getCognome() == cognome;
    //@ assignable \everything;
    public Cliente(String email, String password, String nome, String cognome) {
        super(email, password, "cliente"); // super deve essere la prima istruzione
        /*@ assert email != null && password != null && nome != null && cognome != null; @*/
        this.nome = nome;
        this.cognome = cognome;
        this.prenotazioni = new ArrayList<Prenotazione>();
        /*@ assert this.prenotazioni != null; @*/
    }

    //@ public normal_behavior
    //@ assignable \nothing;
    /*@ pure @*/
    /*@ nullable @*/
    public String getNome() { return nome; }

    //@ public normal_behavior
    //@ requires nome != null;
    //@ assignable \everything;
    public void setNome(String nome) { this.nome = nome; }

    //@ public normal_behavior
    //@ assignable \nothing;
    /*@ pure @*/
    /*@ nullable @*/
    public String getCognome() { return cognome; }

    //@ public normal_behavior
    //@ requires cognome != null;
    //@ assignable \everything;
    public void setCognome(String cognome) { this.cognome = cognome; }

    //@ public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    public List<Prenotazione> getPrenotazioni() { return prenotazioni; }

    //@ public normal_behavior
    //@ requires prenotazioni != null;
    //@ ensures this.prenotazioni != null;
    //@ assignable \everything;
    public void setPrenotazioni(List<Prenotazione> prenotazioni) { this.prenotazioni = prenotazioni; }

    //@ also public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    @Override
    public String toString() {
        return "Cliente{" +
                "nome='" + nome + '\'' +
                ", cognome='" + cognome + '\'' +
                ", prenotazioni=" + prenotazioni +
                '}';
    }
}
