package it.unisa.application.utilities;

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
}
