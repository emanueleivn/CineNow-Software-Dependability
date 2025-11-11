package integration.gestione_catena;

import integration.BaseIntegrationTest;
import it.unisa.application.sottosistemi.gestione_catena.view.AddFilmServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.Part;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.sql.ResultSet;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class AddFilmServletIT extends BaseIntegrationTest {

    // Wrapper per testare i metodi protected
    public static class TestableAddFilmServlet extends AddFilmServlet {
        @Override
        public void doPost(HttpServletRequest req, HttpServletResponse resp)
                throws jakarta.servlet.ServletException, java.io.IOException {
            super.doPost(req, resp);
        }

        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp)
                throws jakarta.servlet.ServletException, java.io.IOException {
            super.doGet(req, resp);
        }
    }

    private TestableAddFilmServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servlet = new TestableAddFilmServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
    }

    // ---------------------------------------------------
    //                TEST DI SUCCESSO
    // ---------------------------------------------------

    @Test
    void doGet_ok() throws Exception {
        when(request.getRequestDispatcher("/WEB-INF/jsp/aggiungiFilm.jsp")).thenReturn(dispatcher);
        servlet.doGet(request, response);
        verify(dispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void addFilm_ok() throws Exception {
        Part part = mock(Part.class);
        byte[] imageBytes = "fakeImage".getBytes();
        InputStream stream = new ByteArrayInputStream(imageBytes);

        when(request.getParameter("titolo")).thenReturn("Matrix");
        when(request.getParameter("durata")).thenReturn("130");
        when(request.getParameter("descrizione")).thenReturn("Film di fantascienza");
        when(request.getParameter("genere")).thenReturn("Sci-Fi");
        when(request.getParameter("classificazione")).thenReturn("T");
        when(request.getPart("locandina")).thenReturn(part);
        when(part.getSize()).thenReturn((long) imageBytes.length);
        when(part.getInputStream()).thenReturn(stream);

        servlet.doPost(request, response);

        try (ResultSet rs = connection.createStatement()
                .executeQuery("SELECT COUNT(*) AS c FROM film WHERE titolo='Matrix'")) {
            assertTrue(rs.next());
            assertEquals(1, rs.getInt("c"), "Il film dovrebbe essere stato inserito correttamente");
        }

        verify(response).sendRedirect(contains("/catalogo"));
        verify(dispatcher, never()).forward(any(), any());
    }

    // ---------------------------------------------------
    //                TEST DI FALLIMENTO
    // ---------------------------------------------------

    @RepeatedTest(5)
    void addFilm_locandinaMancante() throws Exception {
        when(request.getParameter("titolo")).thenReturn("Film senza immagine");
        when(request.getParameter("durata")).thenReturn("100");
        when(request.getParameter("descrizione")).thenReturn("Descrizione test");
        when(request.getParameter("genere")).thenReturn("Azione");
        when(request.getParameter("classificazione")).thenReturn("T");
        when(request.getPart("locandina")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(dispatcher);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(any());
    }

    @RepeatedTest(5)
    void addFilm_durataNonValida_zeroONegativa() throws Exception {
        Part part = mock(Part.class);
        InputStream stream = new ByteArrayInputStream("img".getBytes());
        when(part.getSize()).thenReturn(3L);
        when(part.getInputStream()).thenReturn(stream);

        when(request.getParameter("titolo")).thenReturn("Film durata errata");
        when(request.getParameter("durata")).thenReturn("0");
        when(request.getParameter("descrizione")).thenReturn("Descrizione ok");
        when(request.getParameter("genere")).thenReturn("Azione");
        when(request.getParameter("classificazione")).thenReturn("T");
        when(request.getPart("locandina")).thenReturn(part);
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(dispatcher);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(any());
    }

    @RepeatedTest(5)
    void addFilm_datiNonValidi_stringheVuote() throws Exception {
        Part part = mock(Part.class);
        InputStream stream = new ByteArrayInputStream("img".getBytes());
        when(part.getSize()).thenReturn(3L);
        when(part.getInputStream()).thenReturn(stream);

        when(request.getParameter("titolo")).thenReturn("");
        when(request.getParameter("durata")).thenReturn("100");
        when(request.getParameter("descrizione")).thenReturn("");
        when(request.getParameter("genere")).thenReturn("");
        when(request.getParameter("classificazione")).thenReturn("");
        when(request.getPart("locandina")).thenReturn(part);
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(dispatcher);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(any());
    }

    @RepeatedTest(5)
    void addFilm_datiMancanti_nullValues() throws Exception {
        when(request.getParameter("titolo")).thenReturn(null);
        when(request.getParameter("durata")).thenReturn(null);
        when(request.getParameter("descrizione")).thenReturn(null);
        when(request.getParameter("genere")).thenReturn(null);
        when(request.getParameter("classificazione")).thenReturn(null);
        when(request.getPart("locandina")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(dispatcher);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(any());
    }

}
