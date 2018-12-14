package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.ExpressionOperator;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;
import org.smtlib.CharSequenceReader;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.command.C_assert;
import org.smtlib.command.C_check_sat;
import org.smtlib.command.C_declare_fun;
import org.smtlib.command.C_exit;
import org.smtlib.command.C_set_info;
import org.smtlib.command.C_set_logic;
import org.smtlib.command.C_set_option;
import org.smtlib.impl.SMTExpr.Let;
import org.smtlib.impl.SMTExpr.FcnExpr;
import org.smtlib.impl.Sort;

import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

public class SMTLIBParser {

    public SMTProblem problem;

    private Set<Variable> letContext;

    public SMTLIBParser() {
        problem = new SMTProblem();
        letContext = new HashSet<>();
    }

    public static SMTProblem parseSMTProgram(String input) throws
            IOException,
            IParser.ParserException,
            SMTLIBParserException {
        SMT smt = new SMT();

        ISource toBeParsed = smt.smtConfig.smtFactory.createSource(new CharSequenceReader(new StringReader(input)),
                                                                   null);
        IParser parser = smt.smtConfig.smtFactory.createParser(smt.smtConfig, toBeParsed);
        SMTLIBParser smtParser = new SMTLIBParser();

        while (!parser.isEOD()) {
            ICommand cmd = parser.parseCommand();
            if (cmd instanceof C_declare_fun) {
                smtParser.processDeclareFun((C_declare_fun) cmd);
            }
            else if (cmd instanceof C_assert) {
                smtParser.processAssert((C_assert) cmd);
            }
            else if (cmd instanceof C_check_sat){
                //It is okay, if check_sat is the last command in the chain, but it is just ignored.
                if(!parser.isEOD()) {
                    cmd = parser.parseCommand();
                    if(!(cmd instanceof C_exit)) {
                        throw new SMTLIBParserNotSupportedException(
                                "Check sat is only at the end of a smt problem allowed.");
                    }
                }
            } else if (cmd instanceof C_set_info || cmd instanceof C_set_logic){
                //It is safe to ignore the info commands.
            }
            else {
                throw new SMTLIBParserNotSupportedException("Cannot pare the following command: " + cmd);
            }
        }
        return smtParser.problem;
    }

    public Expression processAssert(C_assert cmd) throws SMTLIBParserException {
        Expression res = processExpression(cmd.expr());
        problem.addAssertion(res);
        return res;
    }

    public void processDeclareFun(C_declare_fun cmd) throws SMTLIBParserException {
        if (cmd.argSorts().size() != 0) {
            throw new SMTLIBParserNotSupportedException(
                    "Cannot convert the declared function, because argument size is not null. Might be implemented in" +
                    " the future.");
        }
        if (!(cmd.resultSort() instanceof Sort.Application)) {
            throw new SMTLIBParserException("Could only convert type of type Sort.Application");
        }
        Sort.Application application = (Sort.Application) cmd.resultSort();
        Type type = TypeMap.getType(application.toString());
        if (type == null) {
            throw new SMTLIBParserExceptionInvalidMethodCall(
                    "Could not resolve type declared in function: " + application.toString());
        }
        Variable var = Variable.create(type, cmd.symbol().toString());
        problem.addVariable(var);
    }

    private <E> Expression<E> processArgument(IExpr arg) throws SMTLIBParserException {
        Expression<E> resolved = null;
        if (arg instanceof ISymbol) {
            resolved = resolveSymbol((ISymbol) arg);
        }
        else if (arg instanceof INumeral) {
            resolved = resolveNumeral((INumeral) arg);
        }
        else if (arg instanceof IDecimal) {
            resolved = resolveDecimal((IDecimal) arg);
        }
        else if (arg instanceof FcnExpr) {
            resolved = processFunctionExpression((FcnExpr) arg);
        }
        else if (arg instanceof Let) {
            resolved = processLetExpression((Let) arg);
        }
        else {
            throw new SMTLIBParserNotSupportedException("The arguments type is not supported: " + arg.getClass());
        }
        return successfulArgumentProcessing(resolved, arg);
    }

    private Expression processExpression(IExpr expr) throws SMTLIBParserException {
        Expression res = null;
        if (expr instanceof FcnExpr) {
            res = processFunctionExpression((FcnExpr) expr);
        }
        else if (expr instanceof Let) {
            res = processLetExpression((Let) expr);
        }
        else {
            throw new SMTLIBParserNotSupportedException("Cannot pare the subexpression of type: " + expr.getClass());
        }
        return res;
    }

    private Expression processLetExpression(Let sExpr) throws SMTLIBParserException {
        List<Variable> parameters = new ArrayList();
        Map<Variable, Expression> parameterValues = new HashMap<>();
        for (IExpr.IBinding binding : sExpr.bindings()) {
            Expression parameterValue = processExpression(binding.expr());
            Variable parameter = Variable.create(parameterValue.getType(), binding.parameter().value());
            parameters.add(parameter);
            parameterValues.put(parameter, parameterValue);
        }
        letContext.addAll(parameters);
        Expression mainValue = processExpression(sExpr.expr());
        letContext.removeAll(parameters);
        return LetExpression.create(parameters, parameterValues, mainValue);
    }

    private Expression processFunctionExpression(FcnExpr sExpr) throws SMTLIBParserException {
        String operatorStr = sExpr.head().headSymbol().value();
        ExpressionOperator operator = ExpressionOperator.fromString(FunctionOperatorMap.getjConstraintOperatorName(
                operatorStr));
        Queue<Expression> convertedArguments = new LinkedList<>();
        for (IExpr arg : sExpr.args()) {
            Expression jExpr = processArgument(arg);
            convertedArguments.add(jExpr);
        }
        return createExpression(operator, convertedArguments);
    }

    private Expression createExpression(ExpressionOperator operator, Queue<Expression> arguments) throws
            SMTLIBParserNotSupportedException,
            SMTLIBParserExceptionInvalidMethodCall {
        Expression expr = arguments.poll();
        if (arguments.peek() == null) {
            if (operator == NumericOperator.MINUS && expr != null) {
                expr = UnaryMinus.create(expr);
            }
            else {
                arguments.add(expr);
                throw new SMTLIBParserExceptionInvalidMethodCall("It is strict required, that an operator is " +
                                                                 "passed together with at least two arguments in the " +
                                                                 "queue" + ".\n" + "This call got passed operator: " +
                                                                 operator + " arguments: " + arguments);
            }
        }
        while (arguments.peek() != null) {
            Expression next = arguments.poll();
            if (operator instanceof NumericOperator) {
                expr = NumericCompound.create(expr, (NumericOperator) operator, next);
            }
            else if (operator instanceof LogicalOperator) {
                expr = PropositionalCompound.create(expr, (LogicalOperator) operator, next);
            }
            else if (operator instanceof BitvectorOperator) {
                expr = BitvectorExpression.create(expr, (BitvectorOperator) operator, next);
            }
            else if (operator instanceof NumericComparator) {
                expr = NumericBooleanExpression.create(expr, (NumericComparator) operator, next);
            }
            else {
                throw new SMTLIBParserNotSupportedException(
                        "Cannot convert the following operator class: " + operator.getClass());
            }
        }
        return expr;
    }


    private Constant resolveDecimal(IDecimal decimal) {
        return Constant.create(BuiltinTypes.DECIMAL, decimal.value());
    }

    private Constant resolveNumeral(INumeral numeral) {
        return Constant.create(BuiltinTypes.INTEGER, numeral.value());
    }

    private Variable resolveSymbol(ISymbol symbol) {
        for (Variable var : problem.variables) {
            if (var.getName().equals(symbol.value())) {
                return var;
            }
        }
        for (Variable parameter : letContext) {
            if (parameter.getName().equals(symbol.value())) {
                return parameter;
            }
        }
        return null;
    }

    private <E> Expression<E> successfulArgumentProcessing(Expression<E> expr, IExpr arg) throws SMTLIBParserException {
        if (expr == null) {
            throw new SMTLIBParserException("Cannot process the following argument: " + arg);
        }
        return expr;
    }

}
