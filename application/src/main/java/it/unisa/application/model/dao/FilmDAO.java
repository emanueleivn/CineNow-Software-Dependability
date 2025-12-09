package it.unisa.application.model.dao;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.entity.Film;

import javax.sql.DataSource;
import java.sql.*;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;

public class FilmDAO {
    //@ spec_public
    private final DataSource ds;

    private final static Logger logger = Logger.getLogger(FilmDAO.class.getName());

    /*@ public normal_behavior
      @   assignable \everything;
      @   ensures this.ds != null;
      @*/
    public FilmDAO() {
        this.ds = DataSourceSingleton.getInstance();
    }

    /*@ public normal_behavior
      @   requires film != null;
      @   assignable \everything;
      @   ensures \result ==> film.getId() >= 0;
      @*/
    public boolean create(Film film) {
        if(film == null) {
            logger.severe("Film null");
            return false;
        }
        String sql = "INSERT INTO film (titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) VALUES (?, ?, ?, ?, ?, ?, ?)";
        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql, Statement.RETURN_GENERATED_KEYS)) {
            ps.setString(1, film.getTitolo());
            ps.setString(2, film.getGenere());
            ps.setString(3, film.getClassificazione());
            ps.setInt(4, film.getDurata());
            ps.setBytes(5, film.getLocandina());
            ps.setString(6, film.getDescrizione());
            ps.setBoolean(7, film.isProiettato());
            int affectedRows = ps.executeUpdate();
            if (affectedRows > 0) {
                ResultSet rs = ps.getGeneratedKeys();
                if (rs.next()) {
                    film.setId(rs.getInt(1));
                }
                return true;
            }
        } catch (SQLException e) {
            logger.severe(e.getMessage());
        }
        return false;
    }

    /*@ public normal_behavior
      @   requires id >= 0;
      @   assignable \everything;
      @   ensures \result == null || \result.getId() == id;
      @*/
    public /*@ nullable @*/ Film retrieveById(int id) {
        String sql = "SELECT id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato FROM film WHERE id = ?";
        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setInt(1, id);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                return new Film(
                        rs.getInt("id"),
                        rs.getString("titolo"),
                        rs.getString("genere"),
                        rs.getString("classificazione"),
                        rs.getInt("durata"),
                        rs.getBytes("locandina"),
                        rs.getString("descrizione"),
                        rs.getBoolean("is_proiettato")
                );
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
    public /*@ non_null @*/ List<Film> retrieveAll() {
        List<Film> films = new ArrayList<>();
        String sql = "SELECT id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato FROM film";
        try (Connection connection = ds.getConnection();
             Statement stmt = connection.createStatement();
             ResultSet rs = stmt.executeQuery(sql)) {
            while (rs.next()) {
                films.add(new Film(
                        rs.getInt("id"),
                        rs.getString("titolo"),
                        rs.getString("genere"),
                        rs.getString("classificazione"),
                        rs.getInt("durata"),
                        rs.getBytes("locandina"),
                        rs.getString("descrizione"),
                        rs.getBoolean("is_proiettato")
                ));
            }
        } catch (SQLException e) {
            logger.severe(e.getMessage());
        }
        return films;
    }

}
