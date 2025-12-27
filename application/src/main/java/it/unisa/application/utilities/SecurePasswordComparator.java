package it.unisa.application.utilities;

import java.security.MessageDigest;

/**
 * Utility class for secure password comparison to prevent timing attacks.
 */
public class SecurePasswordComparator {

    /**
     * Compares two password hashes in constant time to prevent timing attacks.
     * This method ensures that the comparison takes the same amount of time
     * regardless of how many characters match.
     *
     * @param hash1 the first password hash
     * @param hash2 the second password hash
     * @return true if the hashes match, false otherwise
     */
    public static boolean secureCompare(String hash1, String hash2) {
        if (hash1 == null || hash2 == null) {
            return hash1 == hash2;
        }

        // Convert to byte arrays for constant-time comparison
        byte[] a = hash1.getBytes();
        byte[] b = hash2.getBytes();

        // If lengths differ, still compare to maintain constant time
        int length = Math.max(a.length, b.length);
        int result = a.length ^ b.length;

        // Compare all bytes in constant time
        for (int i = 0; i < length; i++) {
            byte byteA = (i < a.length) ? a[i] : 0;
            byte byteB = (i < b.length) ? b[i] : 0;
            result |= byteA ^ byteB;
        }

        return result == 0;
    }

    /**
     * Alternative implementation using MessageDigest.isEqual for constant-time comparison.
     * This is the preferred method as it uses a built-in secure comparison.
     *
     * @param hash1 the first password hash
     * @param hash2 the second password hash
     * @return true if the hashes match, false otherwise
     */
    public static boolean secureCompareDigest(String hash1, String hash2) {
        if (hash1 == null || hash2 == null) {
            return hash1 == hash2;
        }

        byte[] a = hash1.getBytes();
        byte[] b = hash2.getBytes();

        return MessageDigest.isEqual(a, b);
    }
}

