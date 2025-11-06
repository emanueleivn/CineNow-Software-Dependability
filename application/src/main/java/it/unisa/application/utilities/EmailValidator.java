package it.unisa.application.utilities;

public class EmailValidator implements ValidatorStrategy {
    private static final String EMAIL_PATTERN = "^[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\\.[A-Za-z]{2,}$";

    public boolean validate(String campo){
        if (!isEmpty(campo))
            return campo.matches(EMAIL_PATTERN);
        return false;
    }

}
