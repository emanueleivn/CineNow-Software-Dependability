package it.unisa.application.utilities;

public interface ValidatorStrategy {
    boolean validate(String campo);
    default boolean isEmpty(String campo) {
        if (campo == null)
            return true;
        return campo.trim().isEmpty();
    }

    default boolean containsInvalidCharacters(String campo) {
        if (campo == null)
            return true;
        return campo.contains("<") || campo.contains(">") || campo.contains("'") || campo.contains("\"") ||
                campo.contains(";") || campo.contains("=");
    }
}
