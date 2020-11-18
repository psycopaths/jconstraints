package gov.nasa.jpf.constraints.smtlibUtility.parser.utility;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import java.io.File;
import java.io.IOException;
import java.util.Scanner;
import org.smtlib.IParser;

public class ResourceParsingHelper {

  public static File loadResource(final String resourceName) {
    final ClassLoader loader = ResourceParsingHelper.class.getClassLoader();
    return new File(loader.getResource(resourceName).getFile());
  }

  public static SMTProblem parseResourceFile(final String resourceName)
      throws IOException, SMTLIBParserException, IParser.ParserException {
    final ClassLoader loader = ResourceParsingHelper.class.getClassLoader();
    final File inputFile = loadResource(resourceName);

    final StringBuilder content = new StringBuilder();
    try (final Scanner inputScanner = new Scanner(inputFile)) {
      while (inputScanner.hasNextLine()) {
        content.append(inputScanner.nextLine());
      }
    }
    return SMTLIBParser.parseSMTProgram(content.toString());
  }
}
