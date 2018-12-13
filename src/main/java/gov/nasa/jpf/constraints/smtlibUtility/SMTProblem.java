package gov.nasa.jpf.constraints.smtlibUtility;

import com.sun.org.apache.xpath.internal.operations.Bool;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.util.ExpressionUtil;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class SMTProblem {
    public List<Expression<Boolean>> assertions;
    public Set<Variable<?>> variables;

    public SMTProblem(){
        assertions = new ArrayList<>();
        variables = new HashSet<>();
    }
    public void addAssertion(Expression<Boolean> expr){
        assertions.add(expr);
    }

    public void addVariable(Variable var){
        variables.add(var);
    }

    public Expression<Boolean> getAllAssertionsAsConjunction(){
        return ExpressionUtil.and(assertions);
    }

    public SolverContext addProblemToContext(SolverContext ctx){
        for(Expression expr: assertions){
            ctx.add(expr);
        }
        return ctx;
    }
}
