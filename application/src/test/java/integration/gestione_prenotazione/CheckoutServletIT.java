package integration.gestione_prenotazione;

import integration.BaseIT;
import it.unisa.application.sottosistemi.gestione_prenotazione.view.CheckoutServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import static org.mockito.Mockito.*;

class CheckoutServletIT extends BaseIT {

    public static class TestableCheckoutServlet extends CheckoutServlet {
        @Override
        public void doGet(HttpServletRequest request, HttpServletResponse response)
                throws jakarta.servlet.ServletException, java.io.IOException {
            super.doGet(request, response);
        }
    }

    private TestableCheckoutServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setup() {
        servlet = new TestableCheckoutServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);

        when(request.getRequestDispatcher("/WEB-INF/jsp/checkout.jsp")).thenReturn(dispatcher);
    }

    @RepeatedTest(5)
    void checkout_ok() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("1");
        when(request.getParameter("posti")).thenReturn("A1,A2");
        when(request.getParameter("totale")).thenReturn("15.00");

        servlet.doGet(request, response);

        verify(request).setAttribute("proiezioneId", "1");
        verify(request).setAttribute("posti", "A1,A2");
        verify(request).setAttribute("totale", "15.00");
        verify(dispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void checkout_parametriMancanti() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn(null);
        when(request.getParameter("posti")).thenReturn(null);
        when(request.getParameter("totale")).thenReturn(null);

        RequestDispatcher errorDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(errorDispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void checkout_postiNull() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("1");
        when(request.getParameter("posti")).thenReturn(null);  // (2) true
        when(request.getParameter("totale")).thenReturn("15.00");

        RequestDispatcher errorDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(errorDispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void checkout_totaleNull() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("1");
        when(request.getParameter("posti")).thenReturn("A1,A2");
        when(request.getParameter("totale")).thenReturn(null); // (3) true

        RequestDispatcher errorDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(errorDispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void checkout_proiezioneIdBlank() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("");  // (4) true
        when(request.getParameter("posti")).thenReturn("A1,A2");
        when(request.getParameter("totale")).thenReturn("15.00");

        RequestDispatcher errorDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(errorDispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void checkout_postiBlank() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("1");
        when(request.getParameter("posti")).thenReturn("");        // (5) true
        when(request.getParameter("totale")).thenReturn("15.00");

        RequestDispatcher errorDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(errorDispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

    @RepeatedTest(5)
    void checkout_totaleBlank() throws Exception {
        when(request.getParameter("proiezioneId")).thenReturn("1");
        when(request.getParameter("posti")).thenReturn("A1,A2");
        when(request.getParameter("totale")).thenReturn("");       // (6) true

        RequestDispatcher errorDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(errorDispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("errorMessage"), any());
        verify(errorDispatcher).forward(request, response);
    }

}
