package gov.nasa.jpf.constraints.smtlib;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Paths;
import org.smtlib.IParser.ParserException;

public class LoaderUtil {

  public static SMTProblem loadProblemFromResources(String name)
      throws URISyntaxException, IOException, SMTLIBParserException, ParserException {
    URL smtFile = LoaderUtil.class.getClassLoader().getResource(name);
    SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            Files.readAllLines(Paths.get(smtFile.toURI())).stream()
                .reduce(
                    "",
                    (a, b) -> {
                      return b.startsWith(";") ? a : a + b;
                    }));
    return problem;
  }
}
