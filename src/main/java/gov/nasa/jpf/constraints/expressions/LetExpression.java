package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import org.smtlib.TypeChecker;
import org.smtlib.impl.SMTExpr;

import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/*
 * Author: Malte Mues
 */
public class LetExpression extends EqualityExpression {
    private final List<Variable> variables;
    private final Map<Variable, Expression> values;
    private final Expression mainValue;

    public LetExpression(List<Variable> variables, Map<Variable, Expression> values, Expression main){
        super();
        this.variables = variables;
        this.values = values;
        this.mainValue = main;
    }
    public LetExpression(Variable var, Expression value, Expression mainValue) {
        super();
        this.variables = new ArrayList<>();
        this.variables.add(var);
        this.values = new HashMap<>();
        this.values.put(var, value);
        this.mainValue = mainValue;
    }

    public static LetExpression create(Variable var, Expression value, Expression mainValue) {
        return  new LetExpression(var, value, mainValue);
    }

    public static LetExpression create(List<Variable> variables, Map<Variable, Expression> values, Expression main) {
        return  new LetExpression(variables, values, main);
    }

    @Override
    public Boolean evaluate(Valuation values) {
        throw new UnsupportedOperationException("Evaluation of LetExpression is not supported yet.");
    }

    @Override
    public void collectFreeVariables(Collection<? super Variable<?>> variables) {
        throw new UnsupportedOperationException("collectFreeVariables is no supported for LetExpressions yet.");
    }

    @Override
    public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
        throw new UnsupportedOperationException("Visitors are not supported on LetExpression up to now.");
    }

    @Override
    public Expression<?>[] getChildren() {
        throw new UnsupportedOperationException("It is not totally cleare, what is a child in a LetExpression.");
    }

    @Override
    public Expression<?> duplicate(Expression<?>[] newChildren) {
        HashMap<Variable, Expression> copiedValues = new HashMap<>();
        for(Variable var: values.keySet()){
            copiedValues.put(var, values.getOrDefault(var, var).duplicate(newChildren));
        }
        Expression copiedMain = mainValue.duplicate(newChildren);
        return new LetExpression(variables, copiedValues, copiedMain);
    }

    @Override
    public void print(Appendable a, int flags) throws IOException {
        a.append("With (");
        for(Variable var: variables){
            a.append("( " + var.getName() + " == ");
            values.getOrDefault(var, var).print(a, flags);
            a.append(") solve ( ");
        }
        mainValue.print(a, flags);
        a.append(")");
    }

    @Override
    public void printMalformedExpression(Appendable a, int flags)
    throws IOException {
        throw new UnsupportedOperationException("This call is not yet supported.");
    }

    public List<Variable> getParameters() {
        return variables;
    }

    public Map<Variable, Expression> getParameterValues() {
        return values;
    }

    public Expression getMainValue() {
        return mainValue;
    }
}
