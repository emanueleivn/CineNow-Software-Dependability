package it.unisa.application.model.entity;

public class PostoProiezione {
    //@ public invariant posto != null;
    //@ public invariant proiezione != null;

    //@ spec_public
    private Posto posto;
    //@ spec_public
    private Proiezione proiezione;
    //@ spec_public
    private boolean stato;

    //@ public normal_behavior
    //@ requires posto != null && proiezione != null;
    //@ ensures this.posto != null && this.proiezione != null && this.stato == true;
    //@ assignable \everything;
    public PostoProiezione(Posto posto, Proiezione proiezione) {
        this.stato = true;
        this.posto = posto;
        this.proiezione = proiezione;
    }

    public PostoProiezione(Sala sala, char fila, int numero, Proiezione proiezione) {
        this.posto = new Posto(sala, fila, numero);
        this.proiezione = proiezione;
        this.stato = true;
    }

    //@ public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    public Posto getPosto() {
        return posto;
    }

    //@ public normal_behavior
    //@ requires posto != null;
    //@ ensures this.posto != null;
    //@ assignable \everything;
    public void setPosto(Posto posto) {
        this.posto = posto;
    }

    //@ public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    public Proiezione getProiezione() {
        return proiezione;
    }

    //@ public normal_behavior
    //@ requires proiezione != null;
    //@ ensures this.proiezione != null;
    //@ assignable \everything;
    public void setProiezione(Proiezione proiezione) {
        this.proiezione = proiezione;
    }

    //@ public normal_behavior
    //@ assignable \nothing;
    /*@ pure @*/
    public boolean isStato() {
        return stato;
    }

    //@ public normal_behavior
    //@ assignable \everything;
    public void setStato(boolean stato) {
        this.stato = stato;
    }
}
