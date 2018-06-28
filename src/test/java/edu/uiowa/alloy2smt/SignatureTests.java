package edu.uiowa.alloy2smt;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


class SignatureTests
{

    private final String prefix =
            "(set-logic ALL)\n" +
            "(set-option :produce-models true)\n" +
            "(set-option :finite-model-find true)\n" +
            "(declare-sort Atom 0)\n";

    @BeforeEach
    public void beforeEach()
    {
        Utils.resetVariableNameIndex();
    }

    @Test
    public void simpleSignature()
    {

        String input = "sig A {}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void extendedSignatures()
    {

        String input =
                "sig A {}\n" +
                "sig A1 extends A{}\n" +
                "sig A2 extends A{}" ;

        String actual = Utils.translateFromString(input);
        String expected =
                prefix  +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A1 () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A2 () (Set (Tuple Atom )))\n" +
                "(assert (subset this_A1 this_A))\n" +
                "(assert (subset this_A2 this_A))\n" +
                "(assert (= (intersection this_A1 this_A2) (as emptyset (Set (Tuple Atom )))))\n" +
                "(assert (= (intersection this_A2 this_A1) (as emptyset (Set (Tuple Atom )))))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void abstractSignatures1()
    {

        String input =
                "abstract sig A {}\n" +
                "sig A1 extends A{}\n" +
                "sig A2 extends A{}" ;

        String actual = Utils.translateFromString(input);
        String expected =
                prefix  +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A1 () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A2 () (Set (Tuple Atom )))\n" +
                "(assert (subset this_A1 this_A))\n" +
                "(assert (subset this_A2 this_A))\n" +
                "(assert (= (intersection this_A1 this_A2) (as emptyset (Set (Tuple Atom )))))\n" +
                "(assert (= (intersection this_A2 this_A1) (as emptyset (Set (Tuple Atom )))))\n" +
                "(assert (= this_A (union this_A1 this_A2)))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void abstractSignatures2()
    {

        String input =
                "abstract sig A {}\n" +
                "sig A1 extends A{}\n";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix  +
                        "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                        "(declare-fun this_A1 () (Set (Tuple Atom )))\n" +
                        "(assert (subset this_A1 this_A))\n" +
                        "(assert (= this_A this_A1))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void abstractSignatures3()
    {

        String input = "abstract sig A {}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix  +
                "(declare-fun this_A () (Set (Tuple Atom )))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void subsetSignatures()
    {

        String input =
                "sig A,B {}\n" +
                "sig A1 in A+B{}\n" +
                "sig A2 in A{}" ;

        String actual = Utils.translateFromString(input);
        String expected =
                prefix  +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A1 () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A2 () (Set (Tuple Atom )))\n" +
                "(assert (subset this_A1 this_A))\n" +
                "(assert (subset this_A1 this_B))\n" +
                "(assert (subset this_A2 this_A))\n";
        assertEquals(expected, actual);
    }

    @Test
    public void subsetAbstractSignatures()
    {

        String input =
                "abstract sig A,B {}\n" +
                "sig A1 in A+B{}\n" +
                "sig A2 in A{}" ;

        String actual = Utils.translateFromString(input);
        String expected =
                prefix  +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A1 () (Set (Tuple Atom )))\n" +
                "(declare-fun this_A2 () (Set (Tuple Atom )))\n" +
                "(assert (subset this_A1 this_A))\n" +
                "(assert (subset this_A1 this_B))\n" +
                "(assert (subset this_A2 this_A))\n";
        assertEquals(expected, actual);
    }
}