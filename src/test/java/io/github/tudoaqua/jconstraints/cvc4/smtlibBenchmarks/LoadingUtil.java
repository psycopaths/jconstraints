package io.github.tudoaqua.jconstraints.cvc4.smtlibBenchmarks;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;
import org.smtlib.IParser.ParserException;

public class LoadingUtil {

  public static SMTProblem loadProblemFromResources(String name)
      throws URISyntaxException, IOException, SMTLIBParserException, ParserException {
    URL smtFile = QF_LIA_RoundTripTest.class.getClassLoader().getResource(name);
    List<String> input = Files.readAllLines(Paths.get(smtFile.toURI()));
    SMTProblem problem = SMTLIBParser.parseSMTProgram(input
        .stream()
        .reduce("", (a, b) -> {
          return b.startsWith(";") ? a : a + b;
        }));
    return problem;
  }

}
