package unit.test_utilities;

import it.unisa.application.utilities.SecurePasswordComparator;
import org.junit.jupiter.api.RepeatedTest;

import static org.junit.jupiter.api.Assertions.*;

public class SecurePasswordComparatorTest {

    @RepeatedTest(5)
    void testSecureCompareDigest_BothNull_ReturnsTrue() {
        assertTrue(SecurePasswordComparator.secureCompareDigest(null, null));
    }

    @RepeatedTest(5)
    void testSecureCompareDigest_FirstNullSecondNotNull_ReturnsFalse() {
        assertFalse(SecurePasswordComparator.secureCompareDigest(null, "hash"));
    }

    @RepeatedTest(5)
    void testSecureCompareDigest_FirstNotNullSecondNull_ReturnsFalse() {
        assertFalse(SecurePasswordComparator.secureCompareDigest("hash", null));
    }

    @RepeatedTest(5)
    void testSecureCompareDigest_EqualStrings_ReturnsTrue() {
        assertTrue(SecurePasswordComparator.secureCompareDigest("abc123", "abc123"));
    }

    @RepeatedTest(5)
    void testSecureCompareDigest_DifferentStrings_ReturnsFalse() {
        assertFalse(SecurePasswordComparator.secureCompareDigest("abc123", "abc124"));
    }

    @RepeatedTest(5)
    void testSecureCompareDigest_DifferentLength_ReturnsFalse() {
        assertFalse(SecurePasswordComparator.secureCompareDigest("short", "longer"));
    }

    @RepeatedTest(5)
    void testSecureCompareDigest_EmptyStrings_ReturnsTrue() {
        assertTrue(SecurePasswordComparator.secureCompareDigest("", ""));
    }

    @RepeatedTest(5)
    void testSecureCompareDigest_EmptyVsNonEmpty_ReturnsFalse() {
        assertFalse(SecurePasswordComparator.secureCompareDigest("", "x"));
        assertFalse(SecurePasswordComparator.secureCompareDigest("x", ""));
    }

    @RepeatedTest(5)
    void testSecureCompareDigest_CaseSensitive_ReturnsFalse() {
        assertFalse(SecurePasswordComparator.secureCompareDigest("ABC", "abc"));
    }

    @RepeatedTest(5)
    void testSecureCompareDigest_UnicodeSameText_ReturnsTrue() {
        assertTrue(SecurePasswordComparator.secureCompareDigest("pàsswörd", "pàsswörd"));
    }

    @RepeatedTest(5)
    void testSecureCompareDigest_UnicodeDifferentNormalization_MayBeFalse() {
        String composed = "é";          // U+00E9
        String decomposed = "e\u0301";  // U+0065 U+0301

        assertFalse(SecurePasswordComparator.secureCompareDigest(composed, decomposed));
    }
}
