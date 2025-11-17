package unit.test_utilities;

import it.unisa.application.utilities.ValidatorStrategy;
import org.junit.jupiter.api.RepeatedTest;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class ValidatorStrategyTest {
    // Default implementation
    private static class DummyValidator implements ValidatorStrategy {
        @Override
        public boolean validate(String campo) {
            return false;
        }
    }

    @RepeatedTest(5)
    void testIsEmpty() {
        ValidatorStrategy validator = new DummyValidator();

        assertTrue(validator.isEmpty(null));
        assertTrue(validator.isEmpty(""));
        assertTrue(validator.isEmpty("   "));
        assertFalse(validator.isEmpty("abc"));
        assertFalse(validator.isEmpty("  abc  "));
    }

    @RepeatedTest(5)
    void testContainsInvalidCharacters() {
        ValidatorStrategy validator = new DummyValidator();

        assertTrue(validator.containsInvalidCharacters(null));       // per come è implementato
        assertTrue(validator.containsInvalidCharacters("abc<def"));
        assertTrue(validator.containsInvalidCharacters("abc>def"));
        assertTrue(validator.containsInvalidCharacters("abc'def"));
        assertTrue(validator.containsInvalidCharacters("abc\"def"));
        assertTrue(validator.containsInvalidCharacters("abc;def"));
        assertTrue(validator.containsInvalidCharacters("abc=def"));

        assertFalse(validator.containsInvalidCharacters("abcdef"));
    }
}

