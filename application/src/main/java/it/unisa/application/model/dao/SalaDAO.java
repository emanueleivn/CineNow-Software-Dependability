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

public class SalaDAO {
    //@ spec_public
    private final DataSource ds;
    //@ spec_public
    private final static Logger logger = Logger.getLogger(SalaDAO.class.getName());

    /*@ public normal_behavior
      @   assignable \everything;
      @   ensures this.ds != null;
      @*/
    public SalaDAO() {
        this.ds = DataSourceSingleton.getInstance();
    }

    /*@ public normal_behavior
      @   requires id >= 0;
      @   assignable \everything;
      @   ensures \result == null || \result.getId() == id;
      @*/
    public /*@ nullable @*/ Sala retrieveById(int id) {
        String sql = "SELECT id, numero, capienza, id_sede FROM sala WHERE id = ?";
        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setInt(1, id);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                int numeroSala= rs.getInt("numero");
                int capienza = rs.getInt("capienza");
                int idSede= rs.getInt("id_sede");
                return new Sala(id, numeroSala, capienza, new Sede(idSede));
            }
        } catch (SQLException e) {
            logger.log(Level.SEVERE, e.getMessage(), e);
        }
        return null;
    }

    /*@ public normal_behavior
      @   assignable \everything;
      @   ensures \result != null;
      @*/
    public /*@ non_null @*/ List<Sala> retrieveAll() throws SQLException {
        List<Sala> sale = new ArrayList<>();
        String query = "SELECT id, numero, capienza, id_sede FROM sala";

        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(query);
             ResultSet rs = ps.executeQuery()) {

            while (rs.next()) {
                int id = rs.getInt("id");
                int numeroSala= rs.getInt("numero");
                int capienza = rs.getInt("capienza");
                int idSede= rs.getInt("id_sede");
                Sala sala = new Sala(id, numeroSala, capienza, new Sede(idSede));
                sale.add(sala);
            }
        }
        return sale;
    }
}
