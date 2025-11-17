package unit.test_utilities;

import it.unisa.application.utilities.CampoValidator;
import org.junit.jupiter.api.RepeatedTest;

import static org.junit.jupiter.api.Assertions.*;

public class CampoValidatorTest {

    @RepeatedTest(5)
    void testCampoValidator_ValidCampo() {
        CampoValidator validator = new CampoValidator();

        assertTrue(validator.validate("Mario Rossi"));
        assertTrue(validator.validate("Jean-Luc"));
        assertTrue(validator.validate("José Álvarez"));
    }

    @RepeatedTest(5)
    void testCampoValidator_InvalidCampoWithDigits() {
        CampoValidator validator = new CampoValidator();

        assertFalse(validator.validate("Mario Rossi2")); // cifre non ammesse
    }

    @RepeatedTest(5)
    void testCampoValidator_InvalidCampoWithForbiddenChars() {
        CampoValidator validator = new CampoValidator();

        assertFalse(validator.validate("<Mario>"));    // contiene caratteri vietati
    }

    @RepeatedTest(5)
    void testCampoValidator_InvalidCampoEmptyOrNull() {
        CampoValidator validator = new CampoValidator();

        assertFalse(validator.validate(null));
        assertFalse(validator.validate(""));
        assertFalse(validator.validate("   "));
    }
}

