package unit.test_utilities;

import it.unisa.application.utilities.EmailValidator;
import org.junit.jupiter.api.RepeatedTest;

import static org.junit.jupiter.api.Assertions.*;

public class EmailValidatorTest {

    @RepeatedTest(5)
    void testEmailValidator_ValidEmail() {
        EmailValidator validator = new EmailValidator();

        assertTrue(validator.validate("test@example.com"));
        assertTrue(validator.validate("nome.cognome+tag@dominio.co.uk"));
    }

    @RepeatedTest(5)
    void testEmailValidator_InvalidEmail() {
        EmailValidator validator = new EmailValidator();

        assertFalse(validator.validate(null));
        assertFalse(validator.validate(""));
        assertFalse(validator.validate("senza-chiocciola"));
        assertFalse(validator.validate("wrong@domain"));      // senza TLD valido
        assertFalse(validator.validate("wrong@domain.c"));    // TLD di un solo carattere
    }
}

