package unit.test_utilities;

import it.unisa.application.utilities.CampoValidator;
import it.unisa.application.utilities.EmailValidator;
import it.unisa.application.utilities.ValidateStrategyManager;
import it.unisa.application.utilities.ValidatorStrategy;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

public class ValidateStrategyManagerTest {
    ValidateStrategyManager manager;

    @BeforeEach
    void setUp() {
        manager = new ValidateStrategyManager();
    }

    @RepeatedTest(5)
    void testAddAndGetValidator_WithMockito() {
        ValidatorStrategy mockValidator = mock(ValidatorStrategy.class);

        manager.addValidator("custom", mockValidator);

        ValidatorStrategy retrieved = manager.getValidator("custom");
        assertSame(mockValidator, retrieved);
    }

    @RepeatedTest(5)
    void testAddValidator_NullKeyOrNullValidator_NotAdded() {
        ValidatorStrategy mockValidator = mock(ValidatorStrategy.class);

        manager.addValidator(null, mockValidator);
        assertNull(manager.getValidator(null));

        manager.addValidator("chiave", null);
        assertNull(manager.getValidator("chiave"));
    }

    @RepeatedTest(5)
    void testGetValidator_DefaultValidatorsPresent() {

        assertNotNull(manager.getValidator("email"));
        assertTrue(manager.getValidator("email") instanceof EmailValidator);

        assertNotNull(manager.getValidator("campo"));
        assertTrue(manager.getValidator("campo") instanceof CampoValidator);

        assertNull(manager.getValidator("nonEsiste"));
    }

    @RepeatedTest(5)
    void testValidate_AllValid() {
        Map<String, String> inputs = new HashMap<>();
        inputs.put("email", "test@example.com");
        inputs.put("campo", "Mario Rossi");

        assertTrue(manager.validate(inputs));
    }

    @RepeatedTest(5)
    void testValidate_InvalidEmailReturnsFalse() {
        Map<String, String> inputs = new HashMap<>();
        inputs.put("email", "email-non-valida");
        inputs.put("campo", "Mario Rossi");

        assertFalse(manager.validate(inputs));
    }

    @RepeatedTest(5)
    void testValidate_UnknownKeyIsIgnored() {
        Map<String, String> inputs = new HashMap<>();
        inputs.put("sconosciuto", "qualunque valore");

        // non essendoci validator associato alla chiave, il metodo deve restituire true
        assertTrue(manager.validate(inputs));
    }

    @RepeatedTest(5)
    void testValidate_UsesMockValidator() {
        ValidatorStrategy mockValidator = mock(ValidatorStrategy.class);

        manager.addValidator("mockKey", mockValidator);

        Map<String, String> inputs = new HashMap<>();
        inputs.put("mockKey", "valore");

        when(mockValidator.validate("valore")).thenReturn(true);
        assertTrue(manager.validate(inputs));
        verify(mockValidator).validate("valore");

        when(mockValidator.validate("valore")).thenReturn(false);
        assertFalse(manager.validate(inputs));
    }

    @RepeatedTest(5)
    void testValidateAll_ReturnsErrorMessagesForInvalidFields() {
        String[] campi = {"1234", "!!!!"};

        String result = manager.validateAll(campi);

        assertFalse(result.isEmpty());
        assertTrue(result.contains("email non valido"));
        assertTrue(result.contains("campo non valido"));
        assertFalse(result.endsWith(","));   // non deve terminare con virgola
    }
}
