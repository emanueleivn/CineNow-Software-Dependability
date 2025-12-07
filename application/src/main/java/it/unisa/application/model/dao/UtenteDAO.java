package it.unisa.application.model.dao;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.entity.Utente;
import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.logging.Level;
import java.util.logging.Logger;

public class UtenteDAO {
    //@ spec_public
    private final DataSource ds;
    //@ spec_public
    private static final Logger logger = Logger.getLogger(UtenteDAO.class.getName());

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures ds != null;
      @*/
    public UtenteDAO() {
        this.ds = DataSourceSingleton.getInstance();
    }


    /*@ public normal_behavior
      @   requires utente != null;
      @   assignable \everything;
      @   ensures \result ==> utente.getEmail() != null;
      @*/
    public boolean create(Utente utente) {
        if (utente == null) {
            logger.warning("Utente nullo o dati mancanti");
            return false;
        }
        String sql = "INSERT INTO utente (email, password, ruolo) VALUES (?, ?, ?)";
        try (Connection conn = ds.getConnection();
             PreparedStatement stmt = conn.prepareStatement(sql)) {
            stmt.setString(1, utente.getEmail());
            stmt.setString(2, utente.getPassword());
            stmt.setString(3, utente.getRuolo());
            return stmt.executeUpdate() > 0;
        } catch (SQLException e) {
            logger.log(Level.SEVERE, "Errore durante creazione utente", e);
            return false;
        }
    }

    /*@ public normal_behavior
      @   requires email != null;
      @   assignable \nothing;
      @   ensures \result == null || \result.getEmail().equals(email);
      @*/
    public Utente retrieveByEmail(String email) {
        String sql = "SELECT email, password, ruolo " +
                "FROM utente " +
                "WHERE email = ?";
        try (Connection conn = ds.getConnection();
             PreparedStatement stmt = conn.prepareStatement(sql)) {
            stmt.setString(1, email);
            try (ResultSet rs = stmt.executeQuery()) {
                if (rs.next()) {
                    String password =  rs.getString("password");
                    String ruolo = rs.getString("ruolo");
                    return new Utente(email,password,ruolo);
                }
            }
        } catch (SQLException e) {
            logger.log(Level.SEVERE, "Errore durante il recupero dell'utente", e);
        }
        return null;
    }
}
