package it.unisa.application.utilities;

public class PasswordValidator implements ValidatorStrategy {
    // Pattern per validazione formato password (non è una password hardcoded)
    private static final String PASSWORD_FORMAT_PATTERN = "^[a-zA-Z0-9!@#$%^&*()_+\\-=?.,]{8,}$";

    public boolean validate(String campo) {
        if (!isEmpty(campo))
            return campo.matches(PASSWORD_FORMAT_PATTERN);
        return false;
    }
}
