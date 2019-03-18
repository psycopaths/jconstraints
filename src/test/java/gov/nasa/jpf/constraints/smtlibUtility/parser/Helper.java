package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import org.smtlib.IParser;

import java.io.File;
import java.io.IOException;
import java.util.Scanner;

public class Helper {

    public static SMTProblem parseFile(String ressourceName) throws IOException,
            SMTLIBParserException,
            IParser.ParserException {
        ClassLoader loader = SMTLIBParserTest.class.getClassLoader();
        File inputFile = new File(loader.getResource(ressourceName).getFile());

        StringBuilder content = new StringBuilder();
        try (Scanner inputScanner = new Scanner(inputFile)) {
            while (inputScanner.hasNextLine()) {
                content.append(inputScanner.nextLine());
            }
        }
        return SMTLIBParser.parseSMTProgram(content.toString());
    }
}
