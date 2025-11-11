package integration;

import org.h2.jdbcx.JdbcDataSource;
import org.h2.tools.RunScript;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;

import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.naming.spi.NamingManager;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;

public abstract class BaseIntegrationTest {

    protected static Connection connection;

    @BeforeAll
    static void initDatabase() throws Exception {
        Class.forName("org.h2.Driver");

        connection = DriverManager.getConnection(
                "jdbc:h2:mem:cinenow;MODE=MySQL;DB_CLOSE_DELAY=-1;DATABASE_TO_UPPER=false",
                "sa", ""
        );

        // Esecuzione script di creazione schema
        try (InputStream is = BaseIntegrationTest.class.getClassLoader().getResourceAsStream("schema.sql")) {
            if (is == null) {
                throw new IllegalStateException("File schema.sql non trovato nel classpath (src/test/resources)");
            }
            RunScript.execute(connection, new InputStreamReader(is, StandardCharsets.UTF_8));
        }

        // H2 DataSource
        JdbcDataSource ds = new JdbcDataSource();
        ds.setURL("jdbc:h2:mem:cinenow;MODE=MySQL;DB_CLOSE_DELAY=-1;DATABASE_TO_UPPER=false");
        ds.setUser("sa");
        ds.setPassword("");

        // Mock del contesto JNDI compatibile con DataSourceSingleton
        if (!NamingManager.hasInitialContextFactoryBuilder()) {
            NamingManager.setInitialContextFactoryBuilder(env -> environment -> new InitialContext(true) {
                @Override
                public Object lookup(String name) throws NamingException {
                    if ("java:comp/env".equals(name)) {
                        return this;
                    }
                    if ("jdbc/CineNowDataSource".equals(name) ||
                            "java:comp/env/jdbc/CineNowDataSource".equals(name)) {
                        return ds;
                    }
                    return null;
                }
            });
        }

    }

    @BeforeEach
    void resetDatabase() throws SQLException {
        List<String> tables = new ArrayList<>();

        try (var rs = connection.getMetaData().getTables(null, null, "%", new String[]{"TABLE"})) {
            while (rs.next()) {
                String schema = rs.getString("TABLE_SCHEM");
                String tableName = rs.getString("TABLE_NAME");

                // Filtra solo le tabelle (null o 'PUBLIC' in H2)
                if (schema != null && !"PUBLIC".equalsIgnoreCase(schema)) {
                    continue;
                }

                // Salta tabelle interne di H2
                if (tableName.startsWith("INFORMATION_SCHEMA") || tableName.startsWith("SYS_")) {
                    continue;
                }

                // Aggiungi solo le tabelle del dominio applicativo
                tables.add(tableName);
            }
        }

        try (var stmt = connection.createStatement()) {
            stmt.execute("SET REFERENTIAL_INTEGRITY FALSE"); // Disabilita vincoli FK
            for (String table : tables) {
                try {
                    stmt.execute("TRUNCATE TABLE " + table);
                } catch (SQLException e) {
                    System.err.println("[H2 RESET] Impossibile truncare tabella " + table + ": " + e.getMessage());
                }
            }
            stmt.execute("SET REFERENTIAL_INTEGRITY TRUE");
        }

    }


    @AfterAll
    static void tearDown() throws SQLException {
        if (connection != null && !connection.isClosed()) {
            connection.close();
        }
    }

    protected void execute(String sql) throws SQLException {
        try (var stmt = connection.createStatement()) {
            stmt.execute(sql);
        }
    }
}
