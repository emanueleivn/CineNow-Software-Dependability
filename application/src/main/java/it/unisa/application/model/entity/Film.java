package it.unisa.application.model.entity;

import java.util.Arrays;

public class Film {
    //@ public invariant id >= 0;
    //@ public invariant titolo != null;
    //@ public invariant durata > 0;

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

    //@ public normal_behavior
    //@ requires id >= 0 && titolo != null && durata > 0;
    //@ ensures this.id >= 0 && this.titolo != null && this.durata > 0;
    //@ assignable \everything;
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
    public String getTitolo() { return titolo; }

    //@ public normal_behavior
    //@ requires titolo != null;
    //@ ensures this.titolo != null;
    //@ assignable \everything;
    public void setTitolo(String titolo) { this.titolo = titolo; }

    //@ public normal_behavior
    //@ assignable \nothing;
    /*@ pure @*/
    public String getGenere() { return genere; }

    //@ public normal_behavior
    //@ assignable \everything;
    public void setGenere(String genere) { this.genere = genere; }

    //@ public normal_behavior
    //@ assignable \nothing;
    /*@ pure @*/
    public String getClassificazione() { return classificazione; }

    //@ public normal_behavior
    //@ assignable \everything;
    public void setClassificazione(String classificazione) { this.classificazione = classificazione; }

    //@ public normal_behavior
    //@ ensures \result > 0;
    //@ assignable \nothing;
    /*@ pure @*/
    public int getDurata() { return durata; }

    //@ public normal_behavior
    //@ requires durata > 0;
    //@ ensures this.durata > 0;
    //@ assignable \everything;
    public void setDurata(int durata) { this.durata = durata; }

    //@ public normal_behavior
    //@ assignable \nothing;
    /*@ pure @*/
    public byte[] getLocandina() { return locandina; }

    //@ public normal_behavior
    //@ assignable \everything;
    public void setLocandina(byte[] locandina) { this.locandina = locandina; }

    //@ public normal_behavior
    //@ assignable \nothing;
    /*@ pure @*/
    public String getDescrizione() { return descrizione; }

    //@ public normal_behavior
    //@ assignable \everything;
    public void setDescrizione(String descrizione) { this.descrizione = descrizione; }

    //@ public normal_behavior
    //@ assignable \nothing;
    /*@ pure @*/
    public boolean isProiettato() { return isProiettato; }

    //@ public normal_behavior
    //@ assignable \everything;
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
