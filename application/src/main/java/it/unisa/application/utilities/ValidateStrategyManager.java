package it.unisa.application.utilities;

import java.util.HashMap;
import java.util.Map;

public class ValidateStrategyManager {
    private final Map<String, ValidatorStrategy> validators;

    public ValidateStrategyManager() {
        validators = new HashMap<>();
        validators.put("email", new EmailValidator());
        validators.put("campo", new CampoValidator());
    }

    public void addValidator(String key, ValidatorStrategy validator) {
        if (key != null && validator != null)
            validators.put(key, validator);
    }

    public ValidatorStrategy getValidator(String key) {
        if (validators.containsKey(key)) {
            return validators.get(key);
        }
        return null;
    }

    public boolean validate(Map<String, String> inputs) {
        for (Map.Entry<String, String> entry : inputs.entrySet()) {
            String key = entry.getKey();
            String value = entry.getValue();
            ValidatorStrategy validator = validators.get(key);
            if (validator != null && !validator.validate(value)) {
                return false;
            }
        }
        return true;
    }

    public String validateAll(String[] campi) {
        String result = "";
        int processed = 0;

        for(Map.Entry<String, ValidatorStrategy> entry : validators.entrySet()) {
            String key = entry.getKey();
            ValidatorStrategy validator = entry.getValue();

            if (!validator.validate(campi[processed])) {
                result = result.concat(key + " non valido,");
            }
            ++processed;
        }

        if (!result.isEmpty()) {
            result = result.substring(0, result.length() - 1);
        }
        return result;
    }
}
