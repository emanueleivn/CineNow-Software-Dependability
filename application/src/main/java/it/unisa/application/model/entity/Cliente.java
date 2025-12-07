package it.unisa.application.model.entity;

import java.util.ArrayList;
import java.util.List;

public class Cliente extends Utente {
    //@ spec_public
    private String nome;
    //@ spec_public
    private String cognome;
    //@ spec_public
    private List<Prenotazione> prenotazioni;

    /*@ public normal_behavior
      @   requires email != null && password != null && nome != null && cognome != null;
      @   assignable \everything;
      @   ensures this.nome == nome && this.cognome == cognome;
      @   ensures this.prenotazioni != null;
      @*/
    public Cliente(String email, String password, String nome, String cognome) {
        super(email, password, "cliente");
        this.nome = nome;
        this.cognome = cognome;
        this.prenotazioni = new ArrayList<Prenotazione>();
    }

    /*@ public normal_behavior
      @   ensures \result == nome;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getNome() { return nome; }

    /*@ public normal_behavior
      @   requires nome != null;
      @   assignable this.nome;
      @   ensures this.nome == nome;
      @*/
    public void setNome(String nome) { this.nome = nome; }

    /*@ public normal_behavior
      @   ensures \result == cognome;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getCognome() { return cognome; }

    /*@ public normal_behavior
      @   requires cognome != null;
      @   assignable this.cognome;
      @   ensures this.cognome == cognome;
      @*/
    public void setCognome(String cognome) { this.cognome = cognome; }

    /*@ public normal_behavior
      @   ensures \result == prenotazioni;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ List<Prenotazione> storicoOrdini() { return prenotazioni; }

    /*@ public normal_behavior
      @   requires prenotazioni != null;
      @   assignable this.prenotazioni;
      @   ensures this.prenotazioni == prenotazioni;
      @*/
    public void setPrenotazioni(List<Prenotazione> prenotazioni) { this.prenotazioni = prenotazioni; }

    /*@ also public normal_behavior
      @   ensures \result != null;
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure @*/ String toString() {
        return "Cliente{" +
                "nome='" + nome + '\'' +
                ", cognome='" + cognome + '\'' +
                ", prenotazioni=" + prenotazioni +
                '}';
    }
}
