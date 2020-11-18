package gov.nasa.jpf.constraints.smtlibUtility.parser;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper.parseResourceFile;
import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import java.io.IOException;
import org.smtlib.IParser;
import org.testng.annotations.Test;

public class QF_LIA_Test {
  @Test(groups = {"jsmtlib", "base"})
  public void parsingLetAndIte_PRP_3_20_Test()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final SMTProblem problem = parseResourceFile("QF_LIA/prp-3-20.smt2");
    final Expression assertStmt = problem.assertions.get(0);
    assertEquals(assertStmt.getClass(), LetExpression.class);
  }
}
