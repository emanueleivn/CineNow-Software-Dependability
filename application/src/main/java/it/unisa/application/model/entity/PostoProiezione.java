package it.unisa.application.model.entity;

public class PostoProiezione {
    //@ spec_public
    private Posto posto;
    //@ spec_public
    private Proiezione proiezione;
    //@ spec_public
    private boolean stato;

    /*@ public normal_behavior
      @   requires posto != null && proiezione != null;
      @   assignable \everything;
      @   ensures this.posto == posto;
      @   ensures this.proiezione == proiezione;
      @   ensures this.stato == true;
      @*/
    public PostoProiezione(Posto posto, Proiezione proiezione) {
        this.stato = true;
        this.posto = posto;
        this.proiezione = proiezione;
    }

    /*@ public normal_behavior
      @   requires sala != null && proiezione != null;
      @   assignable \everything;
      @   ensures this.posto != null;
      @   ensures this.proiezione == proiezione;
      @   ensures this.stato == true;
      @*/
    public PostoProiezione(Sala sala, char fila, int numero, Proiezione proiezione) {
        this.posto = new Posto(sala, fila, numero);
        this.proiezione = proiezione;
        this.stato = true;
    }

    /*@ public normal_behavior
      @   ensures \result == posto;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Posto getPosto() {
        return posto;
    }

    /*@ public normal_behavior
      @   requires posto != null;
      @   assignable this.posto;
      @   ensures this.posto == posto;
      @*/
    public void setPosto(Posto posto) {
        this.posto = posto;
    }

    /*@ public normal_behavior
      @   ensures \result == proiezione;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Proiezione getProiezione() {
        return proiezione;
    }

    /*@ public normal_behavior
      @   requires proiezione != null;
      @   assignable this.proiezione;
      @   ensures this.proiezione == proiezione;
      @*/
    public void setProiezione(Proiezione proiezione) {
        this.proiezione = proiezione;
    }

    /*@ public normal_behavior
      @   ensures \result == stato;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean isStato() {
        return stato;
    }

    /*@ public normal_behavior
      @   assignable this.stato;
      @   ensures this.stato == stato;
      @*/
    public void setStato(boolean stato) {
        this.stato = stato;
    }
}
