package unit.test_utilities;

import it.unisa.application.utilities.StaticResourcesCacheFilter;
import jakarta.servlet.FilterChain;
import jakarta.servlet.ServletException;
import jakarta.servlet.ServletRequest;
import jakarta.servlet.ServletResponse;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;
import org.mockito.ArgumentCaptor;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

public class StaticResourceCacheFilterTest {

    private StaticResourcesCacheFilter filter;

    private HttpServletRequest request;
    private HttpServletResponse response;
    private FilterChain chain;

    @BeforeEach
    void setUp() {
        filter = new StaticResourcesCacheFilter();

        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        chain = mock(FilterChain.class);
    }

    @RepeatedTest(5)
    void testDoFilter_ImageResource_SetsOneYearCacheHeaders_AndContentType_AndVary() throws IOException, ServletException {
        when(request.getRequestURI()).thenReturn("/static/images/logo.png");

        long before = System.currentTimeMillis();
        filter.doFilter(request, response, chain);
        long after = System.currentTimeMillis();

        // Cache-Control per immagini: 1 anno, public, immutable
        verify(response).setHeader("Cache-Control", "public, max-age=31536000, immutable");

        // Expires coerente con max-age
        ArgumentCaptor<Long> expiresCaptor = ArgumentCaptor.forClass(Long.class);
        verify(response).setDateHeader(eq("Expires"), expiresCaptor.capture());
        long expiresValue = expiresCaptor.getValue();

        assertTrue(expiresValue >= before + 31536000L * 1000);
        assertTrue(expiresValue <= after + 31536000L * 1000);

        // Content-Type
        verify(response).setContentType("image/png");

        // Vary sempre impostato
        verify(response).setHeader("Vary", "Accept-Encoding");

        // chain sempre invocata
        verify(chain).doFilter(request, response);
    }

    @RepeatedTest(5)
    void testDoFilter_JpgResource_SetsOneYearCacheHeaders_AndJpegContentType() throws IOException, ServletException {
        when(request.getRequestURI()).thenReturn("/static/images/photo.JPG"); // case-insensitive

        filter.doFilter(request, response, chain);

        verify(response).setHeader("Cache-Control", "public, max-age=31536000, immutable");
        verify(response).setContentType("image/jpeg");
        verify(response).setHeader("Vary", "Accept-Encoding");
        verify(chain).doFilter(request, response);
    }

    @RepeatedTest(5)
    void testDoFilter_WebpResource_SetsOneYearCacheHeaders_AndWebpContentType() throws IOException, ServletException {
        when(request.getRequestURI()).thenReturn("/static/images/hero.webp");

        filter.doFilter(request, response, chain);

        verify(response).setHeader("Cache-Control", "public, max-age=31536000, immutable");
        verify(response).setContentType("image/webp");
        verify(response).setHeader("Vary", "Accept-Encoding");
        verify(chain).doFilter(request, response);
    }

    @RepeatedTest(5)
    void testDoFilter_CssResource_SetsOneWeekCacheHeaders_AndCssContentType() throws IOException, ServletException {
        when(request.getRequestURI()).thenReturn("/static/css/app.css");

        long before = System.currentTimeMillis();
        filter.doFilter(request, response, chain);
        long after = System.currentTimeMillis();

        verify(response).setHeader("Cache-Control", "public, max-age=604800, immutable");

        ArgumentCaptor<Long> expiresCaptor = ArgumentCaptor.forClass(Long.class);
        verify(response).setDateHeader(eq("Expires"), expiresCaptor.capture());
        long expiresValue = expiresCaptor.getValue();

        assertTrue(expiresValue >= before + 604800L * 1000);
        assertTrue(expiresValue <= after + 604800L * 1000);

        verify(response).setContentType("text/css; charset=UTF-8");
        verify(response).setHeader("Vary", "Accept-Encoding");
        verify(chain).doFilter(request, response);
    }

    @RepeatedTest(5)
    void testDoFilter_JsResource_SetsOneWeekCacheHeaders_AndJsContentType() throws IOException, ServletException {
        when(request.getRequestURI()).thenReturn("/static/js/app.js");

        filter.doFilter(request, response, chain);

        verify(response).setHeader("Cache-Control", "public, max-age=604800, immutable");
        verify(response).setContentType("application/javascript; charset=UTF-8");
        verify(response).setHeader("Vary", "Accept-Encoding");
        verify(chain).doFilter(request, response);
    }

    @RepeatedTest(5)
    void testDoFilter_FontResource_SetsOneYearCacheHeaders_NoContentTypeSetByFilter() throws IOException, ServletException {
        when(request.getRequestURI()).thenReturn("/static/fonts/inter.woff2");

        filter.doFilter(request, response, chain);

        verify(response).setHeader("Cache-Control", "public, max-age=31536000, immutable");
        verify(response).setDateHeader(eq("Expires"), anyLong());

        // setCompressionHeaders non gestisce woff/woff2/ttf/eot: quindi non deve impostare Content-Type
        verify(response, never()).setContentType(anyString());

        verify(response).setHeader("Vary", "Accept-Encoding");
        verify(chain).doFilter(request, response);
    }

    @RepeatedTest(5)
    void testDoFilter_SvgResource_SetsOneYearCacheHeaders_AndSvgContentType() throws IOException, ServletException {
        when(request.getRequestURI()).thenReturn("/static/images/icon.svg");

        filter.doFilter(request, response, chain);

        // svg è considerata immagine -> 1 anno
        verify(response).setHeader("Cache-Control", "public, max-age=31536000, immutable");
        verify(response).setContentType("image/svg+xml");
        verify(response).setHeader("Vary", "Accept-Encoding");
        verify(chain).doFilter(request, response);
    }

    @RepeatedTest(5)
    void testDoFilter_UnknownResource_DoesNotSetCacheHeaders_ButSetsVary_AndCallsChain() throws IOException, ServletException {
        when(request.getRequestURI()).thenReturn("/static/other/readme.txt");

        filter.doFilter(request, response, chain);

        // Nessuna regola cache applicabile
        verify(response, never()).setHeader(eq("Cache-Control"), anyString());
        verify(response, never()).setDateHeader(eq("Expires"), anyLong());

        // Nessun content type per .txt in setCompressionHeaders
        verify(response, never()).setContentType(anyString());

        // Però Vary e chain sono sempre eseguiti
        verify(response).setHeader("Vary", "Accept-Encoding");
        verify(chain).doFilter(request, response);
    }

    @RepeatedTest(5)
    void testDoFilter_RequestAndResponseAreHttpTypes_AssumedCastIsUsed() throws IOException, ServletException {
        // Questo test “documenta” il comportamento: il filtro fa cast a HttpServletRequest/Response.
        // Se qualcuno passasse un ServletRequest non-HTTP, sarebbe ClassCastException (comportamento implicito).
        ServletRequest nonHttpRequest = mock(ServletRequest.class);
        ServletResponse nonHttpResponse = mock(ServletResponse.class);

        assertThrows(ClassCastException.class, () -> filter.doFilter(nonHttpRequest, nonHttpResponse, chain));
    }
}
