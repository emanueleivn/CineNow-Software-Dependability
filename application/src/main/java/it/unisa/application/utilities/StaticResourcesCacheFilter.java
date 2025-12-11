package it.unisa.application.utilities;

import jakarta.servlet.*;
import jakarta.servlet.annotation.WebFilter;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import java.io.IOException;

/**
 * Filtro per gestire la cache e la compressione delle risorse statiche.
 * Migliora le performance e l'EcoIndex della pagina.
 */
@WebFilter(urlPatterns = {"/static/*"})
public class StaticResourcesCacheFilter implements Filter {

    private static final long ONE_YEAR_IN_SECONDS = 31536000L;
    private static final long ONE_WEEK_IN_SECONDS = 604800L;

    @Override
    public void init(FilterConfig filterConfig) throws ServletException {
        // Inizializzazione del filtro
    }

    @Override
    public void doFilter(ServletRequest request, ServletResponse response, FilterChain chain)
            throws IOException, ServletException {

        HttpServletRequest httpRequest = (HttpServletRequest) request;
        HttpServletResponse httpResponse = (HttpServletResponse) response;

        String uri = httpRequest.getRequestURI().toLowerCase();

        // Imposta header di cache in base al tipo di risorsa
        if (isImageResource(uri)) {
            setCacheHeaders(httpResponse, ONE_YEAR_IN_SECONDS, true);
        } else if (isCssOrJsResource(uri)) {
            setCacheHeaders(httpResponse, ONE_WEEK_IN_SECONDS, true);
        } else if (isFontResource(uri)) {
            setCacheHeaders(httpResponse, ONE_YEAR_IN_SECONDS, true);
        }

        setCompressionHeaders(httpResponse, uri);
        httpResponse.setHeader("Vary", "Accept-Encoding");

        chain.doFilter(request, response);
    }

    @Override
    public void destroy() {
        // Cleanup del filtro
    }

    private boolean isImageResource(String uri) {
        return uri.endsWith(".png") || uri.endsWith(".jpg") || uri.endsWith(".jpeg")
                || uri.endsWith(".gif") || uri.endsWith(".webp") || uri.endsWith(".svg")
                || uri.endsWith(".ico");
    }

    private boolean isCssOrJsResource(String uri) {
        return uri.endsWith(".css") || uri.endsWith(".js");
    }

    private boolean isFontResource(String uri) {
        return uri.endsWith(".woff") || uri.endsWith(".woff2")
                || uri.endsWith(".ttf") || uri.endsWith(".eot");
    }

    private void setCacheHeaders(HttpServletResponse response, long maxAgeSeconds, boolean isPublic) {
        String cacheControl = (isPublic ? "public" : "private") + ", max-age=" + maxAgeSeconds + ", immutable";
        response.setHeader("Cache-Control", cacheControl);
        long expiresTime = System.currentTimeMillis() + (maxAgeSeconds * 1000);
        response.setDateHeader("Expires", expiresTime);
    }

    private void setCompressionHeaders(HttpServletResponse response, String uri) {
        if (uri.endsWith(".css")) {
            response.setContentType("text/css; charset=UTF-8");
        } else if (uri.endsWith(".js")) {
            response.setContentType("application/javascript; charset=UTF-8");
        } else if (uri.endsWith(".webp")) {
            response.setContentType("image/webp");
        } else if (uri.endsWith(".png")) {
            response.setContentType("image/png");
        } else if (uri.endsWith(".jpg") || uri.endsWith(".jpeg")) {
            response.setContentType("image/jpeg");
        } else if (uri.endsWith(".svg")) {
            response.setContentType("image/svg+xml");
        }
    }
}

