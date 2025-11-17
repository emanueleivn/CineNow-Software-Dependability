package unit.test_utilities;

import it.unisa.application.utilities.PasswordValidator;
import org.junit.jupiter.api.RepeatedTest;

import static org.junit.jupiter.api.Assertions.*;

public class PasswordValidatorTest {

    @RepeatedTest(5)
    void testPasswordValidator_ValidPassword() {
        PasswordValidator validator = new PasswordValidator();

        assertTrue(validator.validate("Abcdef12"));     // 8 caratteri, alfanumerica
        assertTrue(validator.validate("P@ssw0rd!"));    // con caratteri speciali ammessi
    }

    @RepeatedTest(5)
    void testPasswordValidator_InvalidPassword_TooShort() {
        PasswordValidator validator = new PasswordValidator();

        assertFalse(validator.validate("Abc12!"));      // meno di 8 caratteri
    }

    @RepeatedTest(5)
    void testPasswordValidator_InvalidPassword_NullOrEmpty() {
        PasswordValidator validator = new PasswordValidator();

        assertFalse(validator.validate(null));
        assertFalse(validator.validate(""));
        assertFalse(validator.validate("   "));
    }

    @RepeatedTest(5)
    void testPasswordValidator_InvalidPassword_ForbiddenChars() {
        PasswordValidator validator = new PasswordValidator();

        // carattere non previsto dal pattern (es: spazio)
        assertFalse(validator.validate("Abcdefg "));    // spazio finale
    }
}
