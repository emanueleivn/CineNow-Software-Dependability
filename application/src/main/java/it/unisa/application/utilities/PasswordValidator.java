package it.unisa.application.utilities;

public class PasswordValidator implements ValidatorStrategy {
    private static final String PASSWORD_PATTERN = "^[a-zA-Z0-9!@#$%^&*()_+\\-=?.,]{8,}$";

    public boolean validate(String campo) {
        if (!isEmpty(campo))
            return campo.matches(PASSWORD_PATTERN);
        return false;
    }
}
