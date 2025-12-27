package it.unisa.application.utilities;

public class PasswordValidator implements ValidatorStrategy {
    // Regex pattern for password validation - not a hardcoded password
    private static final String VALIDATION_REGEX = "^[a-zA-Z0-9!@#$%^&*()_+\\-=?.,]{8,}$";

    public boolean validate(String campo) {
        if (!isEmpty(campo))
            return campo.matches(VALIDATION_REGEX);
        return false;
    }
}
