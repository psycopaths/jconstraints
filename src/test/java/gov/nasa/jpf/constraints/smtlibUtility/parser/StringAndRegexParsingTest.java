package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import java.io.IOException;
import org.smtlib.IParser;

public class StringAndRegexParsingTest {
  public static void main(String args[])
      throws IOException, SMTLIBParserException, IParser.ParserException {
    System.out.println("hi");
    SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            "(declare-fun PCTEMP_LHS_1 () Bool)\n"
                + "(declare-fun PCTEMP_LHS_3 () String)\n"
                + "(declare-fun PCTEMP_LHS_4_idx_0 () String)\n"
                + "(declare-fun PCTEMP_LHS_5 () String)\n"
                + "(declare-fun T0_24 () String)\n"
                + "(declare-fun T_12 () Bool)\n"
                + "(declare-fun T_13 () Bool)\n"
                + "(declare-fun T_14 () Bool)\n"
                + "(declare-fun T_15 () Bool)\n"
                + "(declare-fun T_16 () Bool)\n"
                + "(declare-fun T_17 () Bool)\n"
                + "(declare-fun T_18 () Bool)\n"
                + "(declare-fun T_19 () Bool)\n"
                + "(declare-fun T_1a () Bool)\n"
                + "(declare-fun T_1b () Bool)\n"
                + "(declare-fun T_1c () Bool)\n"
                + "(declare-fun T_2 () Bool)\n"
                + "(declare-fun T_3 () Int)\n"
                + "(declare-fun T_4 () Int)\n"
                + "(declare-fun T_6 () Int)\n"
                + "(declare-fun T_7 () Bool)\n"
                + "(declare-fun T_8 () Bool)\n"
                + "(declare-fun T_9 () Int)\n"
                + "(declare-fun T_a () Bool)\n"
                + "(declare-fun T_b () Bool)\n"
                + "(declare-fun T_c () Int)\n"
                + "(declare-fun T_d () Bool)\n"
                + "(declare-fun T_e () Bool)\n"
                + "(declare-fun var_0xINPUT_39034 () String)\n"
                + "(assert (= T_2 (not PCTEMP_LHS_1)))\n"
                + "(assert T_2)\n"
                + "(assert (= T_3 (str.len var_0xINPUT_39034)))\n"
                + "(assert (= T_4 (div T_3 10)))\n"
                + "(assert (= T_6 (str.len var_0xINPUT_39034)))\n"
                + "(assert (= T_7 (< 70 T_6)))\n"
                + "(assert (= T_8 (not T_7)))\n"
                + "(assert T_8)\n"
                + "(assert (= T_9 (str.len var_0xINPUT_39034)))\n"
                + "(assert (= T_a (< 70 T_9)))\n"
                + "(assert (= T_b (not T_a)))\n"
                + "(assert T_b)\n"
                + "(assert (= T_c (str.len var_0xINPUT_39034)))\n"
                + "(assert (= T_d (< 70 T_c)))\n"
                + "(assert (= T_e (not T_d)))\n"
                + "(assert T_e)\n"
                + "(assert (= PCTEMP_LHS_3 var_0xINPUT_39034))\n"
                + "(assert (= T0_24 PCTEMP_LHS_4_idx_0))\n"
                + "(assert (= T0_24 PCTEMP_LHS_3))\n"
                + "(assert (= T_12 (= PCTEMP_LHS_5 \"[object\")))\n"
                + "(assert (= T_13 (not T_12)))\n"
                + "(assert T_13)\n"
                + "(assert (= T_15 (not T_14)))\n"
                + "(assert T_15)\n"
                + "(assert (= T_17 (not T_16)))\n"
                + "(assert T_17)\n"
                + "(assert (= T_19 (not T_18)))\n"
                + "(assert T_19)\n"
                + "(assert (= T_1b (not T_1a)))\n"
                + "(assert T_1b)\n"
                + "(assert T_1c)\n"
                + "(check-sat)");
    System.out.println("Assertions: " + problem.getAllAssertionsAsConjunction());
  }
}
