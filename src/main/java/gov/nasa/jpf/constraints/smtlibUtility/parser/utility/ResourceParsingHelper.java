package gov.nasa.jpf.constraints.smtlibUtility.parser.utility;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import org.smtlib.IParser;

import java.io.File;
import java.io.IOException;
import java.util.Scanner;

public class ResourceParsingHelper {

    public static SMTProblem parseResourceFile(final String ressourceName) throws
            IOException,
            SMTLIBParserException,
            IParser.ParserException {
        final ClassLoader loader = ResourceParsingHelper.class.getClassLoader();
        final File inputFile = new File(loader.getResource(ressourceName).getFile());

        final StringBuilder content = new StringBuilder();
        try (final Scanner inputScanner = new Scanner(inputFile)) {
            while (inputScanner.hasNextLine()) {
                content.append(inputScanner.nextLine());
            }
        }
        return SMTLIBParser.parseSMTProgram(content.toString());
    }
}
