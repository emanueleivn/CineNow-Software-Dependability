package it.unisa.application.model.entity;

import java.util.Arrays;

public class Film {
    //@ spec_public
    private int id;
    //@ spec_public
    private String titolo;
    //@ spec_public
    private String genere;
    //@ spec_public
    private String classificazione;
    //@ spec_public
    private int durata;
    //@ spec_public
    private byte[] locandina;
    //@ spec_public
    private String descrizione;
    //@ spec_public
    private boolean isProiettato;

    //@ public invariant id >= 0;
    //@ public invariant titolo != null;
    //@ public invariant genere != null;
    //@ public invariant classificazione != null;
    //@ public invariant durata > 0;
    //@ public invariant locandina != null;
    //@ public invariant descrizione != null;

    /*@ public normal_behavior
      @   requires id >= 0;
      @   requires titolo != null && genere != null && classificazione != null;
      @   requires durata > 0;
      @   requires descrizione != null;
      @   requires locandina != null;   // se vuoi permettere "nessuna locandina", passa new byte[0]
      @   assignable \nothing;
      @   ensures this.id == id && this.titolo == titolo && this.genere == genere
      @           && this.classificazione == classificazione && this.durata == durata
      @           && this.locandina == locandina && this.descrizione == descrizione
      @           && this.isProiettato == isProiettato;
      @*/
    public Film(int id, String titolo, String genere, String classificazione, int durata,
                byte[] locandina, String descrizione, boolean isProiettato) {
        this.id = id;
        this.titolo = titolo;
        this.genere = genere;
        this.classificazione = classificazione;
        this.durata = durata;
        this.locandina = locandina;
        this.descrizione = descrizione;
        this.isProiettato = isProiettato;
    }

    /*@ public normal_behavior
      @   ensures \result == id;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getId() { return id; }

    /*@ public normal_behavior
      @   requires id >= 0;
      @   assignable this.id;
      @   ensures this.id == id;
      @*/
    public void setId(int id) { this.id = id; }

    /*@ public normal_behavior
      @   ensures \result == titolo;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getTitolo() { return titolo; }

    /*@ public normal_behavior
      @   requires titolo != null;
      @   assignable this.titolo;
      @   ensures this.titolo == titolo;
      @*/
    public void setTitolo(String titolo) { this.titolo = titolo; }

    /*@ public normal_behavior
      @   ensures \result == genere;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getGenere() { return genere; }

    /*@ public normal_behavior
      @   requires genere != null;
      @   assignable this.genere;
      @   ensures this.genere == genere;
      @*/
    public void setGenere(String genere) { this.genere = genere; }

    /*@ public normal_behavior
      @   ensures \result == classificazione;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getClassificazione() { return classificazione; }

    /*@ public normal_behavior
      @   requires classificazione != null;
      @   assignable this.classificazione;
      @   ensures this.classificazione == classificazione;
      @*/
    public void setClassificazione(String classificazione) { this.classificazione = classificazione; }

    /*@ public normal_behavior
      @   ensures \result == durata;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getDurata() { return durata; }

    /*@ public normal_behavior
      @   requires durata > 0;
      @   assignable this.durata;
      @   ensures this.durata == durata;
      @*/
    public void setDurata(int durata) { this.durata = durata; }

    /*@ public normal_behavior
      @   ensures \result == locandina;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ byte[] getLocandina() { return locandina; }

    /*@ public normal_behavior
      @   requires locandina != null;
      @   assignable this.locandina;
      @   ensures this.locandina == locandina;
      @*/
    public void setLocandina(byte[] locandina) { this.locandina = locandina; }

    /*@ public normal_behavior
      @   ensures \result == descrizione;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getDescrizione() { return descrizione; }

    /*@ public normal_behavior
      @   requires descrizione != null;
      @   assignable this.descrizione;
      @   ensures this.descrizione == descrizione;
      @*/
    public void setDescrizione(String descrizione) { this.descrizione = descrizione; }

    /*@ public normal_behavior
      @   ensures \result == isProiettato;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean isProiettato() { return isProiettato; }

    /*@ public normal_behavior
      @   assignable this.isProiettato;
      @   ensures this.isProiettato == proiettato;
      @*/
    public void setProiettato(boolean proiettato) { isProiettato = proiettato; }

    //@ also public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    @Override
    public String toString() {
        return "Film{" +
                "id=" + id +
                ", titolo='" + titolo + '\'' +
                ", genere='" + genere + '\'' +
                ", classificazione='" + classificazione + '\'' +
                ", durata=" + durata +
                ", locandina='" + Arrays.toString(locandina) + '\'' +
                ", descrizione='" + descrizione + '\'' +
                ", isProiettato=" + isProiettato +
                '}';
    }
}
