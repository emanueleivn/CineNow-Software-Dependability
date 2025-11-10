package it.unisa.application.model.dao;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.entity.*;

import javax.sql.DataSource;
import java.sql.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Logger;

public class PrenotazioneDAO {
    private final DataSource ds;
    private final static Logger logger = Logger.getLogger(PrenotazioneDAO.class.getName());
    public PrenotazioneDAO() {
        this.ds = DataSourceSingleton.getInstance();
    }

    public boolean create(Prenotazione prenotazione) {
        if(prenotazione == null || prenotazione.getCliente() == null || prenotazione.getProiezione() == null) {
            logger.severe("Prenotazione, Cliente or Proiezione is null");
            return false;
        }
        String sql = "INSERT INTO prenotazione (email_cliente, id_proiezione) VALUES (?, ?)";
        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql, Statement.RETURN_GENERATED_KEYS)) {
            ps.setString(1, prenotazione.getCliente().getEmail());
            ps.setInt(2, prenotazione.getProiezione().getId());
            int affectedRows = ps.executeUpdate();
            if (affectedRows > 0) {
                ResultSet rs = ps.getGeneratedKeys();
                if (rs.next()) {
                    prenotazione.setId(rs.getInt(1));
                }
                return true;
            }
        } catch (SQLException e) {
            logger.severe(e.getMessage());
        }
        return false;
    }
    
    public Prenotazione retrieveById(int id) {
        String sql = "SELECT * FROM prenotazione WHERE id = ?";
        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setInt(1, id);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                int prenotazioneId = rs.getInt("id");
                Cliente cliente = new Cliente(rs.getString("email_cliente"), "", "", "");
                Proiezione proiezione = new Proiezione(rs.getInt("id_proiezione"));
                
                return new Prenotazione(prenotazioneId, cliente, proiezione);
            }
        } catch (SQLException e) {
            logger.severe(e.getMessage());
        }
        return null;
    }
    
    public List<Prenotazione> retrieveAllByCliente(Cliente cliente) {
        if (cliente == null) {
            logger.severe("Cliente is null");
            return null;
        }
        List<Prenotazione> prenotazioni = new ArrayList<>();
        String sql = "SELECT " +
                "p.id AS prenotazione_id, " +
                "pr.id AS proiezione_id, " +
                "pr.data AS data_proiezione, " +
                "sl.ora_inizio, " +
                "f.id AS film_id, " +
                "f.titolo AS film_titolo, " +
                "f.durata, " +
                "s.id AS sala_id, " +
                "s.numero AS numero_sala, " +
                "pp.fila AS fila_posto, " +
                "pp.numero AS numero_posto " +
                "FROM prenotazione p " +
                "JOIN proiezione pr ON p.id_proiezione = pr.id " +
                "JOIN film f ON pr.id_film = f.id " +
                "JOIN sala s ON pr.id_sala = s.id " +
                "JOIN slot sl ON pr.id_orario = sl.id " +
                "LEFT JOIN occupa o ON o.id_prenotazione = p.id " +
                "LEFT JOIN posto_proiezione pp ON pp.id_sala = o.id_sala AND pp.fila = o.fila AND pp.numero = o.numero AND pp.id_proiezione = pr.id " +
                "WHERE p.email_cliente = ?";

        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setString(1, cliente.getEmail());
            ResultSet rs = ps.executeQuery();

            Map<Integer, Prenotazione> prenotazioneMap = new HashMap<>();

            while (rs.next()) {
                int prenotazioneId = rs.getInt("prenotazione_id");
                Prenotazione prenotazione = prenotazioneMap.getOrDefault(prenotazioneId, null);

                if (prenotazione == null) {
                    Film film = new Film(
                            rs.getInt("film_id"),
                            rs.getString("film_titolo"),
                            null, null,
                            rs.getInt("durata"),
                            null, null,
                            false
                    );

                    SedeDAO sedeDAO = new SedeDAO();
                    SalaDAO salaDAO = new SalaDAO();
                    Sala s = salaDAO.retrieveById(rs.getInt("sala_id"));
                    Sede sede = sedeDAO.retrieveById(s.getSede().getId());
                    Sala sala = new Sala(rs.getInt("sala_id"), rs.getInt("numero_sala"), 0, sede);
                    
                    Slot slot = new Slot(0, rs.getTime("ora_inizio"));
                    
                    Proiezione proiezione = new Proiezione(
                            rs.getInt("proiezione_id"),
                            sala,
                            film,
                            rs.getDate("data_proiezione").toLocalDate(),
                            slot
                    );
                    
                    prenotazione = new Prenotazione(prenotazioneId, cliente, proiezione);
                    prenotazione.setPostiPrenotazione(new ArrayList<>());
                    prenotazioneMap.put(prenotazioneId, prenotazione);
                }

                if (rs.getString("fila_posto") != null && rs.getInt("numero_posto") != 0) {
                    Posto posto = new Posto(
                            prenotazione.getProiezione().getSalaProiezione(),
                            rs.getString("fila_posto").charAt(0),
                            rs.getInt("numero_posto")
                    );

                    PostoProiezione postoProiezione = new PostoProiezione(posto, prenotazione.getProiezione());
                    prenotazione.getPostiPrenotazione().add(postoProiezione);
                }
            }

            prenotazioni.addAll(prenotazioneMap.values());
        } catch (SQLException e) {
            logger.severe(e.getMessage());
        }
        return prenotazioni;
    }
}
