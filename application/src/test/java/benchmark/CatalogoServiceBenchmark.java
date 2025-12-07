package benchmark;

import it.unisa.application.model.dao.FilmDAO;
import it.unisa.application.model.entity.Film;
import it.unisa.application.sottosistemi.gestione_catena.service.CatalogoService;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.mockito.Mockito.*;

/**
 * Benchmark per CatalogoService.
 * Testa getCatalogo() e addFilmCatalogo().
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 15, time = 1)
@Measurement(iterations = 40, time = 1)
@State(Scope.Benchmark)
public class CatalogoServiceBenchmark {

    private CatalogoService catalogoService;
    private List<Film> manyFilms;

    private String validTitolo;
    private int validDurata;
    private String validDescrizione;
    private byte[] validLocandina;
    private String validGenere;
    private String validClassificazione;

    @Setup
    public void setup() {
        validTitolo = "Film di Test";
        validDurata = 120;
        validDescrizione = "Una descrizione valida del film";
        validLocandina = new byte[]{1, 2, 3, 4, 5};
        validGenere = "Drammatico";
        validClassificazione = "PG-13";

        manyFilms = new ArrayList<>();
        for (int i = 1; i <= 100; i++) {
            Film f = new Film(
                    i,
                    "Film " + i,
                    "Azione",
                    "PG-13",
                    100 + i * 10,
                    new byte[0],
                    "Desc " + i,
                    true
            );
            manyFilms.add(f);
        }

        FilmDAO filmDAOMock = mock(FilmDAO.class);

        when(filmDAOMock.retrieveAll()).thenReturn(manyFilms);
        when(filmDAOMock.create(any(Film.class))).thenReturn(true);

        catalogoService = mock(CatalogoService.class, CALLS_REAL_METHODS);
        injectDAO(catalogoService, filmDAOMock);
    }

    private void injectDAO(CatalogoService service, FilmDAO filmDAO) {
        try {
            java.lang.reflect.Field field =
                    CatalogoService.class.getDeclaredField("filmDAO");
            field.setAccessible(true);
            field.set(service, filmDAO);
        } catch (NoSuchFieldException | IllegalAccessException e) {
            throw new RuntimeException("Errore durante l'iniezione del DAO", e);
        }
    }

    @Benchmark
    public void getCatalogoWithManyFilms(Blackhole bh) {
        List<Film> result = catalogoService.getCatalogo();
        bh.consume(result);
    }

    @Benchmark
    public void addFilmCatalogoValid(Blackhole bh) {
        try {
            catalogoService.addFilmCatalogo(
                    validTitolo,
                    validDurata,
                    validDescrizione,
                    validLocandina,
                    validGenere,
                    validClassificazione
            );
            bh.consume(true);
        } catch (Exception e) {
            bh.consume(false);
        }
    }

    @Benchmark
    public void addFilmCatalogoInvalidTitolo(Blackhole bh) {
        try {
            catalogoService.addFilmCatalogo(
                    null,
                    validDurata,
                    validDescrizione,
                    validLocandina,
                    validGenere,
                    validClassificazione
            );
            bh.consume(true);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void addFilmCatalogoInvalidDurata(Blackhole bh) {
        try {
            catalogoService.addFilmCatalogo(
                    validTitolo,
                    -1,
                    validDescrizione,
                    validLocandina,
                    validGenere,
                    validClassificazione
            );
            bh.consume(true);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        }
    }
}
