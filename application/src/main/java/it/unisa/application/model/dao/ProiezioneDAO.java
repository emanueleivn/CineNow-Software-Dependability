package it.unisa.application.model.dao;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.entity.*;

import javax.sql.DataSource;
import java.sql.*;
import java.sql.Date;
import java.time.LocalDate;
import java.time.LocalTime;
import java.util.*;
import java.util.logging.Logger;

public class ProiezioneDAO {
    private final DataSource ds;
    private final static Logger logger = Logger.getLogger(ProiezioneDAO.class.getName());
    public ProiezioneDAO() {
        this.ds = DataSourceSingleton.getInstance();
    }

    public boolean create(Proiezione proiezione) {
        if(proiezione==null){
            logger.severe("Proiezione null");
            return false;
        }

        String insertProiezioneSql = "INSERT INTO proiezione (data, id_film, id_sala, id_orario) VALUES (?, ?, ?, ?)";
        String insertPostiProiezioneSql = """
        INSERT INTO posto_proiezione (id_sala, fila, numero, id_proiezione, stato)
        SELECT posto.id_sala, posto.fila, posto.numero, ?, TRUE
        FROM posto
        WHERE posto.id_sala = ?
        """;

        try (Connection connection = ds.getConnection()) {
            connection.setAutoCommit(false);

            List<Slot> availableSlots = new ArrayList<>();
            try (PreparedStatement psGetSlots = connection.prepareStatement("SELECT id, ora_inizio FROM slot ORDER BY ora_inizio")) {
                try (ResultSet rs = psGetSlots.executeQuery()) {
                    while (rs.next()) {

                        int id = rs.getInt("id");
                        Time ora = rs.getTime("ora_inizio");
                        Slot slot = new Slot(id, ora);
                        availableSlots.add(slot);
                    }
                }
            }

            int slotDurationMinutes = Math.abs(availableSlots.get(1).getOraInizio().toLocalTime().toSecondOfDay()
                    - availableSlots.get(0).getOraInizio().toLocalTime().toSecondOfDay()) / 60;
            int filmDurationMinutes = proiezione.getFilmProiezione().getDurata();
            int requiredSlots = (int) Math.ceil(filmDurationMinutes / (double) slotDurationMinutes);
            Slot startingSlot = proiezione.getOrarioProiezione();
            int startIndex = -1;
            for (int i = 0; i < availableSlots.size(); i++) {
                if (availableSlots.get(i).getId() == startingSlot.getId()) {
                    startIndex = i;
                    break;
                }
            }

            if (startIndex == -1) {
                throw new RuntimeException("Slot di partenza non trovato.");
            }
            int actualSlots = Math.min(requiredSlots, availableSlots.size() - startIndex);
            for (int i = 0; i < actualSlots; i++) {
                Slot currentSlot = availableSlots.get(startIndex + i);
                try (PreparedStatement psProiezione = connection.prepareStatement(insertProiezioneSql, Statement.RETURN_GENERATED_KEYS)) {
                    psProiezione.setDate(1, Date.valueOf(proiezione.getDataProiezione()));
                    psProiezione.setInt(2, proiezione.getFilmProiezione().getId());
                    psProiezione.setInt(3, proiezione.getSalaProiezione().getId());
                    psProiezione.setInt(4, currentSlot.getId());
                    int affectedRows = psProiezione.executeUpdate();
                    if (affectedRows > 0) {
                        try (ResultSet rs = psProiezione.getGeneratedKeys()) {
                            if (rs.next()) {
                                int idProiezione = rs.getInt(1);
                                proiezione.setId(idProiezione);

                                try (PreparedStatement psPostiProiezione = connection.prepareStatement(insertPostiProiezioneSql)) {
                                    psPostiProiezione.setInt(1, idProiezione);
                                    psPostiProiezione.setInt(2, proiezione.getSalaProiezione().getId());
                                    psPostiProiezione.executeUpdate();
                                }
                            }
                        }
                    }
                }
            }
            connection.commit();
            return true;

        } catch (SQLException e) {
            logger.severe("Errore durante la creazione della proiezione: " + e.getMessage());
            try (Connection connection = ds.getConnection()) {
                connection.rollback();
            } catch (SQLException rollbackException) {
                logger.severe(e.getMessage());
            }
        }

        return false;
    }

    public Proiezione retrieveById(int id) {
        String sql = "SELECT * FROM proiezione WHERE id = ?";
        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setInt(1, id);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                int proiezioneId = rs.getInt("id");
                LocalDate dataProiezione = rs.getDate("data").toLocalDate();

                Film film = new Film(rs.getInt("id_film"), "", "", "", 0,new byte[0], "", false);
                Sala sala = new Sala(rs.getInt("id_sala"), 0, 0, new Sede(0));
                Time oraInizio = new Time(0,0,0);
                Slot slotOrario = new Slot(rs.getInt("id_orario"), oraInizio);

                return new Proiezione(proiezioneId, sala, film, dataProiezione, slotOrario);
            }
        } catch (SQLException e) {
            logger.severe("Errore durante il recupero della proiezione: " + e.getMessage());
        }
        return null;
    }

    public List<Proiezione> retrieveByFilm(Film film, Sede sede) {
        if (film == null || sede == null) {
            logger.severe("Film o Sede null");
            return null;
        }
        String sql = """
            SELECT p.*, s.numero AS numero_sala, f.titolo AS titolo_film, f.durata AS durata_film, sl.ora_inizio AS orario
            FROM proiezione p
            JOIN sala s ON p.id_sala = s.id
            JOIN film f ON p.id_film = f.id
            JOIN slot sl ON p.id_orario = sl.id
            WHERE p.id_film = ? AND s.id_sede = ?
            ORDER BY p.data ASC, sl.ora_inizio ASC
            """;

        List<Proiezione> proiezioni = new ArrayList<>();
        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setInt(1, film.getId());
            ps.setInt(2, sede.getId());
            ResultSet rs = ps.executeQuery();
            Map<String, List<Proiezione>> uniqueProiezioni = new HashMap<>();

            while (rs.next()) {
                int id = rs.getInt("id");
                LocalDate dataProiezione = rs.getDate("data").toLocalDate();
                int idSala= rs.getInt("id_sala");
                int numeroSala= rs.getInt("numero_sala");
                Sala sala = new Sala(idSala, numeroSala, 0, sede);

                int idFilm = rs.getInt("id_film");
                String titolo = rs.getString("titolo_film");
                int durata = rs.getInt("durata_film"); // Durata in minuti
                Film filmDetails = new Film(idFilm, titolo, "", "", durata, new byte[0], "", true);

                int idSlot = rs.getInt("id_orario");
                Time ora = rs.getTime("orario");
                Slot slotOrario = new Slot(idSlot, ora);

                Proiezione proiezione = new Proiezione(id, sala, filmDetails, dataProiezione, slotOrario);

                String uniqueKey = proiezione.getFilmProiezione().getTitolo() + "|" +
                        proiezione.getSalaProiezione().getId() + "|" +
                        proiezione.getDataProiezione().toString();


                List<Proiezione> proiezioniPerChiave = uniqueProiezioni.get(uniqueKey);
                if (proiezioniPerChiave == null) {
                    proiezioniPerChiave = new ArrayList<>();
                    uniqueProiezioni.put(uniqueKey, proiezioniPerChiave);
                }
                boolean aggiungiProiezione = true;
                for (Proiezione existingProiezione : proiezioniPerChiave) {
                    int existingEndMinute = existingProiezione.getOrarioProiezione().getOraInizio().toLocalTime().toSecondOfDay() / 60
                            + existingProiezione.getFilmProiezione().getDurata();
                    int currentStartMinute = proiezione.getOrarioProiezione().getOraInizio().toLocalTime().toSecondOfDay() / 60;


                    if (currentStartMinute < existingEndMinute) {
                        aggiungiProiezione = false;
                        break;
                    }
                }

                if (aggiungiProiezione) {
                    proiezioniPerChiave.add(proiezione);
                    uniqueProiezioni.put(uniqueKey, proiezioniPerChiave);
                    proiezioni.add(proiezione);
                }
            }
        } catch (SQLException e) {
            logger.severe(e.getMessage());
        }
        return proiezioni;
    }

    public List<Proiezione> retrieveAllBySede(int sedeId) {
        List<Proiezione> proiezioni = new ArrayList<>();
        String sql = """
            SELECT p.*, s.numero AS numero_sala, f.titolo AS titolo_film, f.durata AS durata_film, sl.ora_inizio AS orario
            FROM proiezione p
            JOIN sala s ON p.id_sala = s.id
            JOIN film f ON p.id_film = f.id
            JOIN slot sl ON p.id_orario = sl.id
            WHERE s.id_sede = ?
            ORDER BY p.data ASC, sl.ora_inizio ASC
            """;

        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setInt(1, sedeId);
            ResultSet rs = ps.executeQuery();


            Map<String, List<Proiezione>> uniqueProiezioni = new HashMap<>();

            while (rs.next()) {
                int idProiezione = rs.getInt("id");

                int idSala = rs.getInt("id_sala");
                int numeroSala = rs.getInt("numero_sala");
                Sala sala = new Sala(idSala, numeroSala, 0, new Sede(sedeId));
                int idFilm = rs.getInt("id_film");
                String titolo = rs.getString("titolo_film");
                int durata = rs.getInt("durata_film");
                Film filmDetails = new Film(idFilm, titolo, "", "", durata, new byte[0], "", true);
                int idOrario = rs.getInt("id_orario");
                Time orario = rs.getTime("orario");
                Slot slotOrario = new Slot(idOrario, orario);
                LocalDate dataProiezione = rs.getDate("data").toLocalDate();
                Proiezione proiezione = new Proiezione(idProiezione, sala, filmDetails, dataProiezione, slotOrario);

                String uniqueKey = proiezione.getFilmProiezione().getTitolo() + "|" +
                        proiezione.getSalaProiezione().getId() + "|" +
                        proiezione.getDataProiezione().toString();

                List<Proiezione> proiezioniPerChiave =
                        uniqueProiezioni.getOrDefault(uniqueKey,
                                new ArrayList<>());


                boolean aggiungiProiezione = true;
                for (Proiezione existingProiezione : proiezioniPerChiave) {
                    int existingEndMinute = existingProiezione.getOrarioProiezione().getOraInizio().toLocalTime().toSecondOfDay() / 60
                            + existingProiezione.getFilmProiezione().getDurata();
                    int currentStartMinute = proiezione.getOrarioProiezione().getOraInizio().toLocalTime().toSecondOfDay() / 60;

                    if (currentStartMinute < existingEndMinute) {
                        aggiungiProiezione = false;
                        break;
                    }
                }

                if (aggiungiProiezione) {
                    proiezioniPerChiave.add(proiezione);
                    uniqueProiezioni.put(uniqueKey, proiezioniPerChiave);
                    proiezioni.add(proiezione);
                }
            }
        } catch (SQLException e) {
            logger.severe(e.getMessage());
        }

        return proiezioni;
    }


    public Proiezione retrieveProiezioneBySalaSlotAndData(int salaId, int slotId, LocalDate data) {
        String sql = "SELECT * FROM proiezione WHERE id_sala = ? AND id_orario = ? AND data = ?";
        try (Connection connection = ds.getConnection(); PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setInt(1, salaId);
            ps.setInt(2, slotId);
            ps.setDate(3, Date.valueOf(data));
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                int proiezioneId = rs.getInt("id");
                LocalDate dataProiezione = rs.getDate("data").toLocalDate();
                Film film = new Film(rs.getInt("id_film"), "", "", "", 0, new byte[0], "", true);
                Sala sala = new Sala(rs.getInt("id_sala"), 0, 0, new Sede(0));
                Slot slot = new Slot(rs.getInt("id_orario"), Time.valueOf(LocalTime.now()));

                return new Proiezione(proiezioneId, sala, film, dataProiezione, slot);
            }
        } catch (SQLException e) {
            logger.severe("Errore durante il recupero della proiezione: " + e.getMessage());
        }
        return null;
    }

}
