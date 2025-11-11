package it.unisa.application.model.entity;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class Sede {
    //@ public invariant id >= 0;
    //@ public invariant sale != null;

    //@ spec_public
    /*@ nullable @*/
    private String nome;
    //@ spec_public
    /*@ nullable @*/
    private String indirizzo;
    //@ spec_public
    private int id;
    //@ spec_public
    private Set<Sala> sale;

    //@ public normal_behavior
    //@ requires id >= 0;
    //@ ensures this.id >= 0 && this.sale != null;
    //@ assignable \everything;
    public Sede(int id){
        this.id = id;
        sale = new HashSet<>();
    }

    //@ public normal_behavior
    //@ requires id >= 0 && nome != null && indirizzo != null;
    //@ ensures this.id >= 0 && this.nome != null && this.indirizzo != null && this.sale != null;
    //@ assignable \everything;
    public Sede(int id, String nome, String indirizzo){
        this.id = id;
        this.nome = nome;
        this.indirizzo = indirizzo;
        this.sale = new HashSet<>();
    }

    //@ public normal_behavior
    //@ ensures \result == this.nome;
    //@ assignable \nothing;
    /*@ pure @*/
    /*@ nullable @*/
    public String getNome() { return nome; }

    //@ public normal_behavior
    //@ requires nome != null;
    //@ ensures this.nome != null;
    //@ assignable \everything;
    public void setNome(String nome) { this.nome = nome; }

    //@ public normal_behavior
    //@ ensures \result == this.indirizzo;
    //@ assignable \nothing;
    /*@ pure @*/
    /*@ nullable @*/
    public String getIndirizzo() { return indirizzo; }

    //@ public normal_behavior
    //@ requires indirizzo != null;
    //@ ensures this.indirizzo != null;
    //@ assignable \everything;
    public void setIndirizzo(String indirizzo) { this.indirizzo = indirizzo; }

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
    public Set<Sala> getSale() { return sale; }

    //@ public normal_behavior
    //@ requires sale != null;
    //@ ensures this.sale != null;
    //@ assignable \everything;
    public void setSale(Set<Sala> sale) { this.sale = sale; }

    // Metodi con lambda/stream: esclusi da ESC/RAC per limitazioni delle specifiche Stream di OpenJML
    //@ skipesc
    //@ skiprac
    public List<Proiezione> getProgrammazione() {
        return sale.stream().
                flatMap(sala -> sala.getProiezioni().stream())
                .collect(Collectors.toList());
    }

    //@ skipesc
    //@ skiprac
    public List<Proiezione> getProiezioniFilm(Film film) {
        return sale.stream()
                .flatMap(sala -> sala.getProiezioni().stream())
                .filter(proiezione -> {
                    Film f = proiezione.getFilmProiezione();
                    return f != null && f.equals(film);
                })
                .collect(Collectors.toList());
    }

    //@ also public normal_behavior
    //@ ensures \result != null;
    //@ assignable \nothing;
    /*@ pure @*/
    @Override
    public String toString() {
        return "Sede{" +
                "nome='" + nome + '\'' +
                ", indirizzo='" + indirizzo + '\'' +
                ", id=" + id +
                ", sale=" + sale +
                '}';
    }
}
