package it.unisa.application.model.entity;

import java.util.Objects;

public class Utente {
    //@ spec_public
    private String email;
    //@ spec_public
    private String password;
    //@ spec_public
    private String ruolo;

    /*@ public normal_behavior
      @   requires email != null && password != null && ruolo != null;
      @   assignable \everything;
      @   ensures this.email == email && this.password == password && this.ruolo == ruolo;
      @*/
    public Utente(String email, String password, String ruolo) {
        this.email = email;
        this.password = password;
        this.ruolo = ruolo;
    }

    /*@ public normal_behavior
      @   ensures \result == email;
      @   assignable \nothing;
      @*/
    public  /*@ pure @*/ String getEmail() { return email; }

    /*@ public normal_behavior
      @   requires email != null;
      @   assignable this.email;
      @   ensures this.email == email;
      @*/
    public void setEmail(String email) { this.email = email; }

    /*@ public normal_behavior
      @   ensures \result == password;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getPassword() { return password; }

    /*@ public normal_behavior
      @   requires password != null;
      @   assignable this.password;
      @   ensures this.password == password;
      @*/
    public void setPassword(String password) { this.password = password; }

    /*@ public normal_behavior
      @   ensures \result == ruolo;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getRuolo() { return ruolo; }

    /*@ public normal_behavior
      @   requires ruolo != null;
      @   assignable this.ruolo;
      @   ensures this.ruolo == ruolo;
      @*/
    public void setRuolo(String ruolo) { this.ruolo = ruolo; }

    /*@ also public normal_behavior
      @   assignable \nothing;
      @*/
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Utente utente = (Utente) o;
        return email.equals(utente.email) && password.equals(utente.password);
    }

    /*@ also public normal_behavior
      @   assignable \nothing;
      @*/
    @Override
    public int hashCode() {
        int result = 17;
        result = 31 * result + email.hashCode();
        result = 31 * result + password.hashCode();
        return result;
    }

    /*@ also public normal_behavior
      @   ensures \result != null;
      @   assignable \nothing;
      @*/
    @Override
    public String toString() {
        return "Utente{" +
                "email='" + email + '\'' +
                ", password='" + password + '\'' +
                ", ruolo='" + ruolo + '\'' +
                '}';
    }
}
