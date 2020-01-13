package gov.nasa.jpf.constraints.smtlibUtility.parser;

import java.io.IOException;

import org.smtlib.IParser;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;

public class StringAndRegexParsingTest {
	public static void main(String args[]) throws IOException, SMTLIBParserException, IParser.ParserException {
		SMTProblem problem = SMTLIBParser.parseSMTProgram("(declare-fun I0_2 () Int)\n" + 
				"(declare-fun I1_2 () Int)\n" + 
				"(declare-fun I2_2 () Int)\n" + 
				"(declare-fun PCTEMP_LHS_1 () String)\n" + 
				"(declare-fun T1_2 () String)\n" + 
				"(declare-fun T2_2 () String)\n" + 
				"(declare-fun T3_2 () String)\n" + 
				"(declare-fun T_2 () Bool)\n" + 
				"(declare-fun var_0xINPUT_2 () String)\n" + 
				"(assert (= I0_2 (- 5 0)))\n" + 
				"(assert (>= 0 0))\n" + 
				"(assert (>= 5 0))\n" + 
				"(assert (<= 5 I1_2))\n" + 
				"(assert (= I2_2 I1_2))\n" + 
				"(assert (= I0_2 (str.len PCTEMP_LHS_1)))\n" + 
				"(assert (= var_0xINPUT_2 (str.++ T1_2 T2_2)))\n" + 
				"(assert (= T2_2 (str.++ PCTEMP_LHS_1 T3_2)))\n" + 
				"(assert (= 0 (str.len T1_2)))\n" + 
				"(assert (= I1_2 (str.len var_0xINPUT_2)))\n" + 
				"(assert (= T_2 (not (= PCTEMP_LHS_1 \"hello\"))))\n" + 
				"(assert T_2)\n" + 
				"(check-sat)");
		System.out.println("Assertions: " + problem.getAllAssertionsAsConjunction()); 
	}
}
