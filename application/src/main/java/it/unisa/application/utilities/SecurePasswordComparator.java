package it.unisa.application.utilities;

import java.security.MessageDigest;

/**
 * Utility class for secure password comparison to prevent timing attacks.
 */
public class SecurePasswordComparator {
    public static boolean secureCompareDigest(String hash1, String hash2) {
        if (hash1 == null || hash2 == null) {
            return hash1 == hash2;
        }

        byte[] a = hash1.getBytes();
        byte[] b = hash2.getBytes();

        return MessageDigest.isEqual(a, b);
    }
}

