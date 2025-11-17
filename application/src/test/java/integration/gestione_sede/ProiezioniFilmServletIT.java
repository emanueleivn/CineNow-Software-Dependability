package integration.gestione_sede;

import integration.BaseIT;
import it.unisa.application.sottosistemi.gestione_sede.view.ProiezioniFilmServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.sql.SQLException;

import static org.mockito.Mockito.*;

public class ProiezioniFilmServletIT extends BaseIT {

    public static class TestableProiezioniFilmServlet extends ProiezioniFilmServlet {
        @Override
        protected void doPost(HttpServletRequest req, HttpServletResponse resp)
                throws ServletException, IOException {
            super.doPost(req, resp);
        }
    }

    private TestableProiezioniFilmServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher successDispatcher;
    private RequestDispatcher errorDispatcher;

    @BeforeEach
    void setup() throws SQLException {
        servlet = new TestableProiezioniFilmServlet();

        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        successDispatcher = mock(RequestDispatcher.class);
        errorDispatcher = mock(RequestDispatcher.class);

        when(request.getRequestDispatcher("/WEB-INF/jsp/proiezioniFilm.jsp"))
                .thenReturn(successDispatcher);
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp"))
                .thenReturn(errorDispatcher);

        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Mercogliano', 'Via Roma 1', 'Avellino', '83100');");
        execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (2, 'Laquila', 'Via Firenze 2', 'L''Aquila', '67100');");

        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (1, 'Inception', 'Sci-Fi', 'T', 148, NULL, 'Thriller fantascientifico', TRUE);");
        execute("INSERT INTO film (id, titolo, genere, classificazione, durata, locandina, descrizione, is_proiettato) " +
                "VALUES (2, 'Matrix', 'Azione', 'T', 136, NULL, 'Azione e realtà virtuale', TRUE);");

        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100);");
        execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (2, 2, 1, 120);");

        execute("INSERT INTO slot (id, ora_inizio) VALUES (1, '18:00:00');");
        execute("INSERT INTO slot (id, ora_inizio) VALUES (2, '21:00:00');");

        execute("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) VALUES (1, CURRENT_DATE, 1, 1, 1);");
        execute("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) VALUES (2, CURRENT_DATE, 2, 2, 2);");
    }

    @RepeatedTest(5)
    void proiezioniFilm_MercoglianoOk() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("1");
        when(request.getParameter("filmId")).thenReturn("1");

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("programmazioneFilm"), any());
        verify(request).setAttribute(eq("filmNome"), eq("Inception"));
        verify(request).setAttribute(eq("sedeNome"), eq("Mercogliano"));
        verify(successDispatcher).forward(request, response);
        verify(errorDispatcher, never()).forward(any(), any());
    }

    @RepeatedTest(5)
    void proiezioniFilm_LAquila_Ok() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("2");
        when(request.getParameter("filmId")).thenReturn("2");

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("programmazioneFilm"), any());
        verify(request).setAttribute(eq("filmNome"), eq("Matrix"));
        verify(request).setAttribute(eq("sedeNome"), eq("Laquila"));
        verify(successDispatcher).forward(request, response);
        verify(errorDispatcher, never()).forward(any(), any());
    }

    @RepeatedTest(5)
    void film_inesistente() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("1");
        when(request.getParameter("filmId")).thenReturn("999");

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
        verify(successDispatcher, never()).forward(any(), any());
    }

    @RepeatedTest(5)
    void programmazioneFilm_null() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("1");
        when(request.getParameter("filmId")).thenReturn("1");
        //NPE
        execute("DELETE FROM sala WHERE id_sede = 1;");

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
        verify(successDispatcher, never()).forward(any(), any());
    }

    @RepeatedTest(5)
    void film_null_ma_programmazione_esiste_per_coprire_condizioni_false() throws Exception {
        // film inesistente → film == null
        when(request.getParameter("filmId")).thenReturn("999");

        // sede esistente con proiezioni → sede != null, programmazioneFilm != null, !empty
        when(request.getParameter("sedeId")).thenReturn("1");

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void sede_inesistente() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("999");
        when(request.getParameter("filmId")).thenReturn("1");

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
        verify(successDispatcher, never()).forward(any(), any());
    }

    @RepeatedTest(5)
    void parametri_non_validi() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("abc");
        when(request.getParameter("filmId")).thenReturn("xyz");

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
        verify(successDispatcher, never()).forward(any(), any());
    }

    @RepeatedTest(5)
    void proiezioni_vuote() throws Exception {
        // film e sede validi ma nessuna proiezione
        execute("DELETE FROM proiezione WHERE id_film = 1 AND id_sala = 1;");

        when(request.getParameter("sedeId")).thenReturn("1");
        when(request.getParameter("filmId")).thenReturn("1");

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
        verify(successDispatcher, never()).forward(any(), any());
    }

    @Test
    void errore_generico_service() throws Exception {
        when(request.getParameter("sedeId")).thenReturn("1");
        when(request.getParameter("filmId")).thenReturn("1");

        // Causerà un NPE interno nel service (sala mancante ma film e sede esistenti)
        execute("DELETE FROM sala WHERE id = 1;");
        execute("DELETE FROM proiezione WHERE id_film = 1;");

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
        verify(successDispatcher, never()).forward(any(), any());
    }

    @Test
    void eccezione_generica_dao() throws Exception {
        // Rende la tabella film non più compatibile con il DAO
        execute("ALTER TABLE film DROP COLUMN titolo;");

        when(request.getParameter("sedeId")).thenReturn("1");
        when(request.getParameter("filmId")).thenReturn("1");

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

}
