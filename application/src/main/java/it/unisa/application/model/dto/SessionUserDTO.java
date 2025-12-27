package it.unisa.application.model.dto;

import it.unisa.application.model.entity.Cliente;
import it.unisa.application.model.entity.GestoreSede;
import it.unisa.application.model.entity.Utente;
import it.unisa.application.utilities.InputSanitizer;

import java.io.Serializable;

/**
 * Data Transfer Object for storing sanitized user information in HTTP sessions.
 * This class acts as a security boundary, ensuring only safe, validated data is stored in sessions.
 */
public class SessionUserDTO implements Serializable {
    private static final long serialVersionUID = 1L;

    private final String email;
    private final String ruolo;
    private final String nome;
    private final String cognome;
    private final Integer sedeId;

    private SessionUserDTO(Builder builder) {
        this.email = builder.email;
        this.ruolo = builder.ruolo;
        this.nome = builder.nome;
        this.cognome = builder.cognome;
        this.sedeId = builder.sedeId;
    }

    /**
     * Creates a safe SessionUserDTO from an Utente entity, sanitizing all string fields.
     *
     * @param utente the user entity to convert
     * @return a sanitized SessionUserDTO
     */
    public static SessionUserDTO fromUtente(Utente utente) {
        if (utente == null) {
            return null;
        }

        Builder builder = new Builder()
                .email(InputSanitizer.sanitize(utente.getEmail()))
                .ruolo(InputSanitizer.sanitize(utente.getRuolo()));

        if (utente instanceof Cliente) {
            Cliente cliente = (Cliente) utente;
            builder.nome(InputSanitizer.sanitize(cliente.getNome()))
                   .cognome(InputSanitizer.sanitize(cliente.getCognome()));
        } else if (utente instanceof GestoreSede) {
            GestoreSede gestoreSede = (GestoreSede) utente;
            if (gestoreSede.getSede() != null) {
                builder.sedeId(gestoreSede.getSede().getId());
            }
        }

        return builder.build();
    }

    // Getters
    public String getEmail() {
        return email;
    }

    public String getRuolo() {
        return ruolo;
    }

    public String getNome() {
        return nome;
    }

    public String getCognome() {
        return cognome;
    }

    public Integer getSedeId() {
        return sedeId;
    }

    // Builder pattern for flexible construction
    public static class Builder {
        private String email;
        private String ruolo;
        private String nome;
        private String cognome;
        private Integer sedeId;

        public Builder email(String email) {
            this.email = email;
            return this;
        }

        public Builder ruolo(String ruolo) {
            this.ruolo = ruolo;
            return this;
        }

        public Builder nome(String nome) {
            this.nome = nome;
            return this;
        }

        public Builder cognome(String cognome) {
            this.cognome = cognome;
            return this;
        }

        public Builder sedeId(Integer sedeId) {
            this.sedeId = sedeId;
            return this;
        }

        public SessionUserDTO build() {
            return new SessionUserDTO(this);
        }
    }
}

