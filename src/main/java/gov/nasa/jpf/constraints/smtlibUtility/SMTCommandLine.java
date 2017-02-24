package gov.nasa.jpf.constraints.smtlibUtility;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import org.smtlib.IParser;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;

public class SMTCommandLine {

    public static void main(String args[]) throws IOException, SMTLIBParserException, IParser.ParserException {
        if(args.length == 1){
            String filename = args[0];
            System.out.println("Trying to parse filename: " + filename);

            StringBuilder builder = new StringBuilder();
            try (BufferedReader reader = new BufferedReader(new FileReader(filename))) {
                builder.append(reader.readLine());
            }
            SMTProblem problem = SMTLIBParser.parseSMTProgram(builder.toString());

            ConstraintSolverFactory factory = ConstraintSolverFactory.getRootFactory();
            ConstraintSolver solver = factory.createSolver();
            ConstraintSolver.Result result = solver.isSatisfiable(problem.getAllAssertionsAsConjunction());
            System.out.println("The result ist: " + result.name());
        }else{
            System.out.println("This script expects at least one filename to solve.");
        }
    }
}
