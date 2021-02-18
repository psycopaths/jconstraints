package gov.nasa.jpf.constraints.smtlib;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import org.smtlib.IParser.ParserException;

public class LoadingUtil {

  public static SMTProblem loadProblemFromResources(String name)
      throws URISyntaxException, IOException, SMTLIBParserException, ParserException {
    URL smtFile = LoadingUtil.class.getClassLoader().getResource(name);
    SMTProblem problem =
        SMTLIBParser.parseSMTProgramFromFile(smtFile.getFile()
        );
    return problem;
  }
}
