package it.unisa.application.model.entity;

import java.util.Objects;

public class Utente {
    //@ spec_public
    private String email;
    //@ spec_public
    private String password;
    //@ spec_public
    private String ruolo;

    //@ public normal_behavior
    //@ requires email != null && password != null && ruolo != null;
    //@ ensures this.email == email && this.password == password && this.ruolo == ruolo;
    //@ assignable \everything;
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

    //@ public normal_behavior
    //@ requires email != null;
    //@ assignable \everything;
    public void setEmail(String email) { this.email = email; }

    //@ public normal_behavior
    //@ ensures \result == password;
    //@ assignable \nothing;
    /*@ pure @*/
    public String getPassword() { return password; }

    //@ public normal_behavior
    //@ requires password != null;
    //@ assignable \everything;
    public void setPassword(String password) { this.password = password; }

    //@ public normal_behavior
    //@ ensures \result == ruolo;
    //@ assignable \nothing;
    /*@ pure @*/
    public String getRuolo() { return ruolo; }

    //@ public normal_behavior
    //@ requires ruolo != null;
    //@ assignable \everything;
    public void setRuolo(String ruolo) { this.ruolo = ruolo; }

    //@ also public normal_behavior
    //@ assignable \nothing;
    /*@ pure @*/
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        // Manteniamo la semantica standard: se o è null o di classe diversa -> false
        if (o == null || getClass() != o.getClass()) return false;
        Utente utente = (Utente) o;
        /*@
          // Dopo il controllo precedente possiamo assumere che 'utente' non sia null
          // e possiamo richiedere esplicitamente al verificatore che i suoi campi
          // rispettino gli invarianti dichiarati nella classe.
          assert utente != null;
          assert utente.email != null;
          assert utente.password != null;
          // Anche per 'this' dichiariamo gli invarianti per aiutare il verificatore
          assert this.email != null;
          assert this.password != null;
        @*/
        // Uso equals sui campi (email e password) noti non-null per evitare problemi
        // con specifiche di libreria complesse (Objects.equals -> CharSequence.jml)
        return email.equals(utente.email) && password.equals(utente.password);
    }

    //@ also public normal_behavior
    //@ assignable \nothing;
    /*@ pure @*/
    @Override
    public int hashCode() {
        int result = 17;
        result = 31 * result + email.hashCode();
        result = 31 * result + password.hashCode();
        return result;
    }

    //@ also public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    @Override
    public String toString() {
        return "Utente{" +
                "email='" + email + '\'' +
                ", password='" + password + '\'' +
                ", ruolo='" + ruolo + '\'' +
                '}';
    }
}
