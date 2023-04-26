package com.CedarDefinitionalImplementation;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

/**
 *  DefinitionalEngineTest.
 */
public class DefinitionalEngineTest {
    @Test
    public void nullTest() {
        DefinitionalEngine engine = new DefinitionalEngine();
        assertEquals("null", engine.isAuthorized_str("{"));
    }
}
