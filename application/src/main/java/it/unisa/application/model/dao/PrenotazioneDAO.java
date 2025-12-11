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

    //@ spec_public
    private final DataSource ds;

    private final static Logger logger = Logger.getLogger(PrenotazioneDAO.class.getName());

    //@ public invariant ds != null;

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures this.ds != null;
      @*/
    public PrenotazioneDAO() {
        this.ds = DataSourceSingleton.getInstance();
    }

    /** Crea una nuova prenotazione nel database. */
    /*@ public normal_behavior
      @   requires prenotazione != null;
      @   requires prenotazione.getCliente() != null;
      @   requires prenotazione.getProiezione() != null;
      @   requires prenotazione.getId() >= 0;
      @   requires prenotazione.getPostiPrenotazione() != null;
      @   assignable \everything;
      @   ensures prenotazione != null;
      @   ensures prenotazione.getCliente() != null;
      @   ensures prenotazione.getProiezione() != null;
      @   ensures \result ==> prenotazione.getId() >= 0;
      @*/
    public boolean create(Prenotazione prenotazione) {
        if (prenotazione == null || prenotazione.getCliente() == null || prenotazione.getProiezione() == null) {
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
                    int newId = rs.getInt(1);
                    // L'invariante di Prenotazione richiede id >= 0, e setId lo fa rispettare.
                    //@ assume newId >= 0;
                    prenotazione.setId(newId);
                }
                return true;
            }
        } catch (SQLException e) {
            String msg = e.getMessage();
            logger.severe(msg != null ? msg : "");
        }
        return false;
    }

    /** Recupera una prenotazione per id. */
    /*@ public normal_behavior
      @   requires id > 0;
      @   assignable \everything;
      @   ensures \result == null
      @        || (\result.getId() >= 0
      @            && \result.getCliente() != null
      @            && \result.getProiezione() != null);
      @*/
    public /*@ nullable @*/ Prenotazione retrieveById(int id) {
        String sql = "SELECT id, email_cliente, id_proiezione FROM prenotazione WHERE id = ?";
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
            String msg = e.getMessage();
            logger.severe(msg != null ? msg : "");
        }
        return null;
    }

    /** Recupera tutte le prenotazioni associate a un certo cliente. */
    /*@ public normal_behavior
      @   requires cliente != null;
      @   requires cliente.getEmail() != null;
      @   assignable \everything;
      @   ensures \result != null;
      @   ensures (\forall int i; 0 <= i && i < \result.size();
      @               \result.get(i) != null
      @            && \result.get(i).getCliente() == cliente);
      @*/
    public /*@ non_null @*/ List<Prenotazione> retrieveAllByCliente(Cliente cliente) {
        if (cliente == null) {
            logger.severe("Cliente is null");
            return null; // percorso impossibile sotto le precondizioni JML
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

            /*@ loop_invariant prenotazioni != null && prenotazioneMap != null;
              @ loop_invariant cliente != null && cliente.getEmail() != null;
              @ loop_invariant (\forall int i; 0 <= i && i < prenotazioni.size();
              @                        prenotazioni.get(i) != null
              @                     && prenotazioni.get(i).getCliente() == cliente);
              @*/
            while (rs.next()) {
                int prenotazioneId = rs.getInt("prenotazione_id");
                Prenotazione prenotazione = prenotazioneMap.get(prenotazioneId);

                if (prenotazione == null) {
                    Film film = new Film(
                            rs.getInt("film_id"),
                            rs.getString("film_titolo"),
                            "", "",
                            rs.getInt("durata"),
                            new byte[0], "",
                            false
                    );

                    SedeDAO sedeDAO = new SedeDAO();
                    SalaDAO salaDAO = new SalaDAO();
                    Sala s = salaDAO.retrieveById(rs.getInt("sala_id"));
                    Sede sede = sedeDAO.retrieveById(s.getSede().getId());
                    Sala sala = new Sala(rs.getInt("sala_id"), rs.getInt("numero_sala"), 1, sede);

                    Slot slot = new Slot(0, rs.getTime("ora_inizio"));

                    Proiezione proiezione = new Proiezione(
                            rs.getInt("proiezione_id"),
                            sala,
                            film,
                            rs.getDate("data_proiezione").toLocalDate(),
                            slot
                    );

                    // Costruiamo la prenotazione usando il Cliente passato:
                    prenotazione = new Prenotazione(prenotazioneId, cliente, proiezione);
                    prenotazione.setPostiPrenotazione(new ArrayList<PostoProiezione>());

                    prenotazioneMap.put(prenotazioneId, prenotazione);
                    prenotazioni.add(prenotazione);
                }

                String fila = rs.getString("fila_posto");
                int numero = rs.getInt("numero_posto");

                if (fila != null && numero != 0) {
                    Posto posto = new Posto(
                            prenotazione.getProiezione().getSalaProiezione(),
                            fila.charAt(0),
                            numero
                    );

                    PostoProiezione postoProiezione =
                            new PostoProiezione(posto, prenotazione.getProiezione());

                    prenotazione.getPostiPrenotazione().add(postoProiezione);
                }
            }

        } catch (SQLException e) {
            String msg = e.getMessage();
            logger.severe(msg != null ? msg : "");
        }
        return prenotazioni;
    }
}
