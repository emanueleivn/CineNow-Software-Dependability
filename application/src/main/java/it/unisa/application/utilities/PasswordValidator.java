package it.unisa.application.utilities;

public class PasswordValidator implements ValidatorStrategy {
    // Regex pattern for password validation - not a hardcoded password
    private static final String VALIDATION_REGEX = "^[a-zA-Z0-9!@#$%^&*()_+\\-=?.,]{8,}$";

    @Override
    public boolean validate(String campo) {
        if (campo != null && !campo.trim().isEmpty()) {
            return campo.matches(VALIDATION_REGEX);
        }
        return false;
    }
}
