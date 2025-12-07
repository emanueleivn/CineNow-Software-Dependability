package it.unisa.application.model.entity;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class Sede {
    //@ spec_public
    private String nome;
    //@ spec_public
    private String indirizzo;
    //@ spec_public
    private int id;
    //@ spec_public
    private Set<Sala> sale;

    /*@ public normal_behavior
      @   requires id >= 0;
      @   assignable \everything;
      @   ensures this.id == id;
      @   ensures this.sale != null;
      @*/
    public Sede(int id){
        this.id = id;
        this.sale = new HashSet<>();
    }

    /*@ public normal_behavior
      @   requires id >= 0;
      @   requires nome != null && indirizzo != null;
      @   assignable \everything;
      @   ensures this.id == id;
      @   ensures this.nome == nome;
      @   ensures this.indirizzo == indirizzo;
      @   ensures this.sale != null;
      @*/
    public Sede(int id, String nome, String indirizzo){
        this.id = id;
        this.nome = nome;
        this.indirizzo = indirizzo;
        this.sale = new HashSet<>();
    }

    /*@ public normal_behavior
      @   ensures \result == this.nome;
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
      @   ensures \result == this.indirizzo;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getIndirizzo() { return indirizzo; }

    /*@ public normal_behavior
      @   requires indirizzo != null;
      @   assignable this.indirizzo;
      @   ensures this.indirizzo == indirizzo;
      @*/
    public void setIndirizzo(String indirizzo) { this.indirizzo = indirizzo; }

    /*@ public normal_behavior
      @   ensures \result == this.id;
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
      @   ensures \result == this.sale;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Set<Sala> getSale() { return sale; }

    /*@ public normal_behavior
      @   requires sale != null;
      @   assignable this.sale;
      @   ensures this.sale == sale;
      @*/
    public void setSale(Set<Sala> sale) { this.sale = sale; }

    // Metodi con lambda/stream: esclusi da ESC/RAC
    //@ skipesc
    //@ skiprac
    public List<Proiezione> getProgrammazione() {
        return sale.stream()
                .flatMap(sala -> sala.getProiezioni().stream())
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
