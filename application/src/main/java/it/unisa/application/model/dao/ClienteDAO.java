package it.unisa.application.model.dao;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.entity.Cliente;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.logging.Logger;
import javax.sql.DataSource;

public class ClienteDAO {
    private final DataSource ds;
    private final static Logger logger = Logger.getLogger(ClienteDAO.class.getName());

    public ClienteDAO() {
        this.ds = DataSourceSingleton.getInstance();
    }

    public boolean create(Cliente cliente) {
        if(cliente == null) {
            logger.severe("cliente null");
            return false;
        }
        String sqlCliente = "INSERT INTO cliente (email, nome, cognome) VALUES (?, ?, ?)";
        try (Connection conn = ds.getConnection()) {
            conn.setAutoCommit(false);
            try (PreparedStatement stmtCliente = conn.prepareStatement(sqlCliente)) {
                UtenteDAO uDao = new UtenteDAO();
                uDao.create(cliente);
                stmtCliente.setString(1, cliente.getEmail());
                stmtCliente.setString(2, cliente.getNome());
                stmtCliente.setString(3, cliente.getCognome());
                stmtCliente.executeUpdate();
                conn.commit();
                return true;
            } catch (SQLException e) {
                conn.rollback();
                logger.severe(e.getMessage());
                return false;
            }
        } catch (SQLException e) {
            logger.severe(e.getMessage());
            return false;
        }
    }

    public Cliente retrieveByEmail(String email, String password) {
        String sql = "SELECT c.email, c.nome, c.cognome " +
                     "FROM cliente c " +
                     "JOIN utente u ON c.email = u.email " +
                     "WHERE u.email = ? AND u.password = ?";
        try (Connection conn = ds.getConnection();
             PreparedStatement stmt = conn.prepareStatement(sql)) {
            stmt.setString(1, email);
            stmt.setString(2, password);
            try (ResultSet rs = stmt.executeQuery()) {
                if (rs.next()) {
                    String nome = rs.getString("nome");
                    String cognome= rs.getString("cognome");
                    Cliente cliente = new Cliente(email, password, nome, cognome);
                    PrenotazioneDAO pDao = new PrenotazioneDAO();
                    cliente.setPrenotazioni(pDao.retrieveAllByCliente(cliente));
                    return cliente;
                }
            }
        } catch (SQLException e) {
            logger.severe(e.getMessage());
        }
        return null;
    }
}
