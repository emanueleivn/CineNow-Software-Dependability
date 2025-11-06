package it.unisa.application.utilities;

public class CampoValidator implements ValidatorStrategy {
    public boolean validate(String campo) {
        return !isEmpty(campo) && !containsInvalidCharacters(campo);
    }
}
