package it.unisa.application.utilities;

public class CampoValidator implements ValidatorStrategy {
    private static final String NAME_PATTERN = "^[A-Za-zÀ-ÿ'\\s-]+$";
    public boolean validate(String campo) {
        return !isEmpty(campo) && !containsInvalidCharacters(campo) && campo.matches(NAME_PATTERN);
    }
}
