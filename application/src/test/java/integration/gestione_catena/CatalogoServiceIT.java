package integration.gestione_catena;

import integration.BaseIntegrationTest;
import it.unisa.application.model.entity.Film;
import it.unisa.application.sottosistemi.gestione_catena.service.CatalogoService;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class CatalogoServiceIT extends BaseIntegrationTest {

    private CatalogoService service;

    @BeforeEach
    void setUp() {
        service = new CatalogoService();
    }

    @RepeatedTest(5)
    void addFilmCatalogo_ok() throws SQLException {
        byte[] img = "imagebytes".getBytes();

        service.addFilmCatalogo(
                "Inception",
                148,
                "Thriller fantascientifico di Nolan",
                img,
                "Sci-Fi",
                "T"
        );

        try (ResultSet rs = connection.createStatement()
                .executeQuery("SELECT COUNT(*) AS c FROM film WHERE titolo = 'Inception'")) {
            assertTrue(rs.next());
            assertEquals(1, rs.getInt("c"));
        }
    }

    @RepeatedTest(5)
    void addFilmCatalogo_parametriNulli_throwsException() {
        byte[] img = "bytes".getBytes();

        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo(null, 120, "descrizione", img, "genere", "T"));

        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("Titolo", -10, "descrizione", img, "genere", "T"));

        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("Titolo", 100, null, img, "genere", "T"));

        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("Titolo", 100, "descrizione", new byte[0], "genere", "T"));

        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("Titolo", 100, "descrizione", img, "", "T"));
    }

    @RepeatedTest(5)
    void addFilmCatalogo_durataZero_throwsException() {
        byte[] img = "bytes".getBytes();
        assertThrows(IllegalArgumentException.class, () ->
                service.addFilmCatalogo("Film", 0, "desc", img, "genere", "T"));
    }

    @RepeatedTest(5)
    void getCatalogo_ok() throws SQLException {
        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (1, 'Matrix', 'Sci-Fi', 'T', 136, NULL, 'Azione e realtà virtuale', TRUE);");
        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (2, 'Avatar', 'Fantasy', 'T', 162, NULL, 'Viaggio su Pandora', TRUE);");

        List<Film> catalogo = service.getCatalogo();

        assertNotNull(catalogo);
        assertEquals(2, catalogo.size());
        assertTrue(catalogo.stream().anyMatch(f -> f.getTitolo().equals("Matrix")));
        assertTrue(catalogo.stream().anyMatch(f -> f.getTitolo().equals("Avatar")));
    }

    @RepeatedTest(5)
    void getCatalogo_vuoto() {
        List<Film> catalogo = service.getCatalogo();
        assertNotNull(catalogo);
        assertTrue(catalogo.isEmpty(), "Il catalogo deve essere vuoto all'inizio");
    }
}
