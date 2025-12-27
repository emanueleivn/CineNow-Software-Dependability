package it.unisa.application.utilities;

import it.unisa.application.model.entity.Cliente;
import it.unisa.application.model.entity.GestoreSede;
import it.unisa.application.model.entity.Utente;

/**
 * Utility class for sanitizing user input to prevent XSS and injection attacks.
 * This class is used to clean data before storing it in HTTP sessions or displaying it.
 */
public class InputSanitizer {

    /**
     * Sanitizes a string by encoding HTML special characters.
     * This prevents XSS attacks and ensures data stored in sessions is safe.
     *
     * @param input the string to sanitize
     * @return the sanitized string, or null if input is null
     */
    public static String sanitize(String input) {
        if (input == null) {
            return null;
        }

        // Remove leading/trailing whitespace
        String sanitized = input.trim();

        // Encode HTML special characters to prevent XSS
        sanitized = sanitized.replace("&", "&amp;")
                           .replace("<", "&lt;")
                           .replace(">", "&gt;")
                           .replace("\"", "&quot;")
                           .replace("'", "&#x27;")
                           .replace("/", "&#x2F;");

        return sanitized;
    }

    /**
     * Validates that a string doesn't contain dangerous characters or patterns.
     *
     * @param input the string to validate
     * @return true if the string is safe, false otherwise
     */
    public static boolean isSafe(String input) {
        if (input == null) {
            return true;
        }

        // Check for common injection patterns
        String dangerous = input.toLowerCase();
        return !dangerous.contains("<script") &&
               !dangerous.contains("javascript:") &&
               !dangerous.contains("onerror=") &&
               !dangerous.contains("onload=") &&
               !dangerous.contains("onclick=") &&
               !dangerous.contains("eval(") &&
               !dangerous.contains("expression(") &&
               !dangerous.contains("vbscript:") &&
               !dangerous.contains("onmouseover=");
    }

    /**
     * Creates a sanitized copy of an Utente object.
     * This method sanitizes all string fields to prevent trust boundary violations
     * when storing user data in HTTP sessions.
     *
     * @param utente the user entity to sanitize
     * @return a new Utente object with sanitized fields, preserving the original type
     */
    public static Utente sanitizeUtente(Utente utente) {
        if (utente == null) {
            return null;
        }

        // Handle Cliente subtype
        if (utente instanceof Cliente) {
            Cliente cliente = (Cliente) utente;
            Cliente sanitizedCliente = new Cliente(
                sanitize(cliente.getEmail()),
                cliente.getPassword(), // Password is already hashed, no need to sanitize
                sanitize(cliente.getNome()),
                sanitize(cliente.getCognome())
            );
            sanitizedCliente.setRuolo(sanitize(cliente.getRuolo()));
            return sanitizedCliente;
        }

        // Handle GestoreSede subtype
        if (utente instanceof GestoreSede) {
            GestoreSede gestoreSede = (GestoreSede) utente;
            GestoreSede sanitizedGestoreSede = new GestoreSede(
                sanitize(gestoreSede.getEmail()),
                gestoreSede.getPassword(), // Password is already hashed
                gestoreSede.getSede() // Sede comes from database, considered trusted
            );
            sanitizedGestoreSede.setRuolo(sanitize(gestoreSede.getRuolo()));
            return sanitizedGestoreSede;
        }

        // Handle base Utente type
        Utente sanitizedUtente = new Utente(
            sanitize(utente.getEmail()),
            utente.getPassword(), // Password is already hashed
            sanitize(utente.getRuolo())
        );
        return sanitizedUtente;
    }
}
