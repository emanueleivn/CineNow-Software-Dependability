package it.unisa.application.model.dao;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.model.entity.Slot;
import javax.sql.DataSource;
import java.sql.*;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

public class SlotDAO {
    //@ spec_public
    private final DataSource ds;
    //@ spec_public
    private static final Logger logger = Logger.getLogger(SlotDAO.class.getName());

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures ds != null;
      @*/
    public SlotDAO() {
        this.ds = DataSourceSingleton.getInstance();
    }

    /*@ public normal_behavior
      @   requires id >= 0;
      @   assignable \nothing;
      @   ensures \result == null || \result.getId() == id;
      @*/
    public Slot retrieveById(int id) {
        String sql = "SELECT * FROM slot WHERE id = ?";
        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setInt(1, id);
            ResultSet rs = ps.executeQuery();
            if(rs.next()){
                Time oraInizio = rs.getTime("ora_inizio");
                return new Slot(id, oraInizio);
            }
        } catch (SQLException e) {
            logger.log(Level.SEVERE, "Errore durante il recupero dello slot", e);
        }
        return null;
    }

    /*@ public normal_behavior
      @   requires proiezione != null;
      @   assignable \nothing;
      @   ensures \result == null || \result.getId() == proiezione.getOrarioProiezione().getId();
      @*/
    public Slot retrieveByProiezione(Proiezione proiezione){
        if (proiezione == null || proiezione.getOrarioProiezione() == null) {
            logger.warning("Proiezione o slot associato null");
            return null;
        }
        String sql = "SELECT * FROM slot WHERE id = ?";
        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setInt(1, proiezione.getOrarioProiezione().getId());
            ResultSet rs = ps.executeQuery();
            if(rs.next()){
                int id = rs.getInt("id");
                Time oraInizio = rs.getTime("ora_inizio");
                return new Slot(id, oraInizio);
            }
        } catch (SQLException e) {
            logger.log(Level.SEVERE, "Errore durante il recupero dello slot per la proiezione" , e);
        }
        return null;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result != null;
      @*/
    public List<Slot> retrieveAllSlots() {
        List<Slot> list = new ArrayList<>();
        String sql = "SELECT * FROM slot ORDER BY ora_inizio";

        try (Connection con = ds.getConnection();
             PreparedStatement ps = con.prepareStatement(sql);
             ResultSet rs = ps.executeQuery()) {

            while (rs.next()) {
                int id = rs.getInt("id");
                Time oraInizio = rs.getTime("ora_inizio");
                list.add(new Slot(id, oraInizio));
            }
        } catch (SQLException e) {
            logger.log(Level.SEVERE, "Errore durante il recupero di tutti gli slot", e);
        }
        return list;
    }
}
