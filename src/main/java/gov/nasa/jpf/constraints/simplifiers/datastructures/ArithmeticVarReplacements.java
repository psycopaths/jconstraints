package gov.nasa.jpf.constraints.simplifiers.datastructures;

import com.google.common.base.Function;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;

import java.util.HashMap;
import java.util.Map;


public class ArithmeticVarReplacements implements Function<Variable<?>, Expression<?>> {

    private Map<Variable, Expression> replacements;

    public ArithmeticVarReplacements(Map<Variable, Expression> replacements) {
        this.replacements = new HashMap(replacements);
    }

    public void putAll(Map<Variable, Expression> addition) {
        replacements.putAll(addition);
    }

    @Override
    public Expression apply(Variable variable) {
        return replacements.getOrDefault(variable, variable);
    }

    @Override
    public boolean equals(Object o) {
        throw new UnsupportedOperationException("This function has no Equivalence");
    }
}
