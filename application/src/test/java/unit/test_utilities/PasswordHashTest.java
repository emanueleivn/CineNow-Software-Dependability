package unit.test_utilities;

import it.unisa.application.utilities.PasswordHash;
import org.junit.jupiter.api.RepeatedTest;

import static org.junit.jupiter.api.Assertions.*;

public class PasswordHashTest {

    @RepeatedTest(5)
    void testPasswordHash_NotNullAndNotEqualToPassword() {
        String password = "password";
        String hashed = PasswordHash.hash(password);

        assertNotNull(hashed);
        assertNotEquals(password, hashed);
    }

    @RepeatedTest(5)
    void testPasswordHash_Deterministic() {
        String password = "password";

        String hash1 = PasswordHash.hash(password);
        String hash2 = PasswordHash.hash(password);

        assertEquals(hash1, hash2);
    }

    @RepeatedTest(5)
    void testPasswordHash_KnownValue() {
        String password = "password";
        // SHA-512("password") calcolato in esadecimale
        String expected = "b109f3bbbc244eb82441917ed06d618b9008dd09b3befd1b5e07394c706a8bb9"
                + "80b1d7785e5976ec049b46df5f1326af5a2ea6d103fd07c95385ffab0cacbc86";

        String actual = PasswordHash.hash(password);

        assertEquals(expected, actual);
    }
}

