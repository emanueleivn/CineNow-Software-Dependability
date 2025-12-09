package it.unisa.application.model.dao;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.entity.Film;
import it.unisa.application.model.entity.Sala;
import it.unisa.application.model.entity.Sede;

import javax.sql.DataSource;
import java.sql.*;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

public class SedeDAO {
    //@ spec_public
    private final DataSource ds;
    //@ spec_public
    private static final Logger logger = Logger.getLogger(SedeDAO.class.getName());

    /*@ public normal_behavior
      @   assignable \everything;
      @   ensures this.ds != null;
      @*/
    public SedeDAO() {
        this.ds = DataSourceSingleton.getInstance();
    }

    /*@ public normal_behavior
      @   requires id >= 0;
      @   assignable \everything;
      @   ensures \result == null || \result.getId() == id;
      @*/
    public /*@ nullable @*/ Sede retrieveById(int id) {
        String sql = "SELECT s.id, s.nome, s.via, s.citta, s.cap FROM sede s WHERE s.id = ?";
        try (Connection connection = ds.getConnection(); PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setInt(1, id);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                String indirizzo = rs.getString("via") + ", " + rs.getString("citta") + ", " + rs.getString("cap");
                return new Sede(rs.getInt("id"), rs.getString("nome"), indirizzo);
            }
        } catch (SQLException e) {
            logger.severe(e.getMessage());
        }
        return null;
    }

    /*@ public normal_behavior
      @   assignable \everything;
      @   ensures \result != null;
      @*/
    public /*@ non_null @*/ List<Sede> retrieveAll() {
        String sql = "SELECT * FROM sede";
        List<Sede> sedi = new ArrayList<>();
        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql);
             ResultSet rs = ps.executeQuery()) {
            while (rs.next()) {
                String indirizzo = rs.getString("via") + ", " + rs.getString("citta") + ", " + rs.getString("cap");
                sedi.add(new Sede(rs.getInt("id"), rs.getString("nome"), indirizzo));
            }
        } catch (SQLException e) {
            logger.log(Level.SEVERE, "Errore durante il recupero delle sedi", e);
        }
        return sedi;
    }

    /*@ public normal_behavior
      @   requires sedeId >= 0;
      @   assignable \everything;
      @   ensures \result != null;
      @*/
    public /*@ non_null @*/ List<Sala> retrieveSaleBySede(int sedeId) {
        List<Sala> sale = new ArrayList<>();
        String sql = "SELECT * FROM sala WHERE id_sede = ?";
        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setInt(1, sedeId);
            try (ResultSet rs = ps.executeQuery()) {
                while (rs.next()) {
                    int salaId = rs.getInt("id");
                    int numero = rs.getInt("numero");
                    int capienza = rs.getInt("capienza");
                    Sala s = new Sala(salaId, numero, capienza, null);
                    sale.add(s);
                }
            }
        } catch (SQLException e) {
            logger.log(Level.SEVERE, "Errore durante il recupero delle sale per la sede", e);
        }
        return sale;
    }

    /*@ public normal_behavior
      @   requires email != null;
      @   assignable \everything;
      @   ensures \result == null || \result.getId() >= 0;
      @*/
    public /*@ nullable @*/ Sede retrieveByGestoreEmail(String email) {
        String sql = "SELECT s.id, s.nome, s.via, s.citta, s.cap FROM sede s JOIN gest_sede gs ON s.id = gs.id_sede WHERE gs.email = ?";
        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setString(1, email);
            try (ResultSet rs = ps.executeQuery()) {
                if (rs.next()) {
                    String indirizzo = rs.getString("via") + ", " + rs.getString("citta") + ", " + rs.getString("cap");
                    return new Sede(rs.getInt("id"), rs.getString("nome"), indirizzo);
                }
            }
        } catch (SQLException e) {
            logger.log(Level.SEVERE, "Errore durante il recupero della sede per l'email", e);
        }
        return null;
    }

    /*@ public normal_behavior
      @   requires sedeId >= 0;
      @   assignable \everything;
      @   ensures \result != null;
      @*/
    public /*@ non_null @*/ List<Film> retrieveFilm(int sedeId) {
        List<Film> filmList = new ArrayList<>();
        String query = """
                SELECT DISTINCT f.id, f.titolo, f.genere, f.classificazione, f.durata, f.locandina, f.descrizione, f.is_proiettato
                FROM film f
                JOIN proiezione p ON f.id = p.id_film
                JOIN sala s ON p.id_sala = s.id
                WHERE s.id_sede = ?
                """;

        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(query)) {
            ps.setInt(1, sedeId);
            try (ResultSet rs = ps.executeQuery()) {
                while (rs.next()) {
                    int identifier = rs.getInt("id");
                    String titolo = rs.getString("titolo");
                    String genere = rs.getString("genere");
                    String classificazione = rs.getString("classificazione");
                    int durata = rs.getInt("durata");
                    byte[] locandina = rs.getBytes("locandina");
                    String descrizione = rs.getString("descrizione");
                    boolean isProiettato = rs.getBoolean("is_proiettato");
                    Film film = new Film(identifier, titolo, genere, classificazione, durata, locandina, descrizione, isProiettato);
                    filmList.add(film);
                }
            }
        } catch (SQLException e) {
            logger.log(Level.SEVERE, "Errore durante il recupero dei film per la sede", e);
        }
        return filmList;
    }
}
