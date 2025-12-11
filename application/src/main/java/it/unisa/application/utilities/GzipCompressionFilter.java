package it.unisa.application.utilities;

import jakarta.servlet.*;
import jakarta.servlet.annotation.WebFilter;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpServletResponseWrapper;
import java.io.*;
import java.util.zip.GZIPOutputStream;

/**
 * Filtro per la compressione GZIP delle risorse statiche.
 * Riduce il peso della pagina e migliora l'EcoIndex.
 */
@WebFilter(urlPatterns = {"/static/*"})
public class GzipCompressionFilter implements Filter {

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
        String acceptEncoding = httpRequest.getHeader("Accept-Encoding");

        // Applica compressione solo per risorse testuali se il client supporta gzip
        if (acceptEncoding != null && acceptEncoding.contains("gzip") && isCompressible(uri)) {
            GzipResponseWrapper gzipResponse = new GzipResponseWrapper(httpResponse);
            try {
                chain.doFilter(request, gzipResponse);
                gzipResponse.finish();
            } finally {
                gzipResponse.close();
            }
        } else {
            chain.doFilter(request, response);
        }
    }

    @Override
    public void destroy() {
        // Cleanup del filtro
    }

    private boolean isCompressible(String uri) {
        return uri.endsWith(".css") || uri.endsWith(".js") || uri.endsWith(".svg");
    }

    private static class GzipResponseWrapper extends HttpServletResponseWrapper {
        private GzipServletOutputStream gzipOutputStream;
        private PrintWriter printWriter;
        private boolean isOutputStreamUsed = false;
        private boolean isWriterUsed = false;

        public GzipResponseWrapper(HttpServletResponse response) {
            super(response);
        }

        @Override
        public ServletOutputStream getOutputStream() throws IOException {
            if (isWriterUsed) {
                throw new IllegalStateException("getWriter() already called");
            }
            if (gzipOutputStream == null) {
                gzipOutputStream = new GzipServletOutputStream(getResponse().getOutputStream());
                setHeader("Content-Encoding", "gzip");
                isOutputStreamUsed = true;
            }
            return gzipOutputStream;
        }

        @Override
        public PrintWriter getWriter() throws IOException {
            if (isOutputStreamUsed) {
                throw new IllegalStateException("getOutputStream() already called");
            }
            if (printWriter == null) {
                gzipOutputStream = new GzipServletOutputStream(getResponse().getOutputStream());
                setHeader("Content-Encoding", "gzip");
                printWriter = new PrintWriter(new OutputStreamWriter(gzipOutputStream, getCharacterEncoding()));
                isWriterUsed = true;
            }
            return printWriter;
        }

        public void finish() throws IOException {
            if (printWriter != null) {
                printWriter.flush();
            }
            if (gzipOutputStream != null) {
                gzipOutputStream.finish();
            }
        }

        public void close() throws IOException {
            if (printWriter != null) {
                printWriter.close();
            }
            if (gzipOutputStream != null) {
                gzipOutputStream.close();
            }
        }
    }

    private static class GzipServletOutputStream extends ServletOutputStream {
        private final GZIPOutputStream gzipOutputStream;

        public GzipServletOutputStream(OutputStream output) throws IOException {
            this.gzipOutputStream = new GZIPOutputStream(output);
        }

        @Override
        public void write(int b) throws IOException {
            gzipOutputStream.write(b);
        }

        @Override
        public void write(byte[] b) throws IOException {
            gzipOutputStream.write(b);
        }

        @Override
        public void write(byte[] b, int off, int len) throws IOException {
            gzipOutputStream.write(b, off, len);
        }

        @Override
        public void flush() throws IOException {
            gzipOutputStream.flush();
        }

        public void finish() throws IOException {
            gzipOutputStream.finish();
        }

        @Override
        public void close() throws IOException {
            gzipOutputStream.close();
        }

        @Override
        public boolean isReady() {
            return true;
        }

        @Override
        public void setWriteListener(WriteListener writeListener) {
            // Non implementato
        }
    }
}

