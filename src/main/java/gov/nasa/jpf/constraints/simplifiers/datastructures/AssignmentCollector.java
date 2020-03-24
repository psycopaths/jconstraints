package gov.nasa.jpf.constraints.simplifiers.datastructures;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.util.ExpressionUtil;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class AssignmentCollector {

    private Map<Variable, List<Expression>> assignments;
    private Map<Variable, List<Expression>> eventuallyPrune;
    private int insideNegation = 0;

    public AssignmentCollector() {
        assignments = new HashMap<>();
        eventuallyPrune = new HashMap<>();
    }

    public void addAssignment(Variable v, Expression e, Expression originalAssignment) {
        List assignmentForVar = assignments.getOrDefault(v, new ArrayList<>());
        assignmentForVar.add(e);
        assignments.put(v, assignmentForVar);

        List prune = eventuallyPrune.getOrDefault(v, new ArrayList<>());
        prune.add(originalAssignment);
        eventuallyPrune.put(v, prune);
    }

    public ArithmeticVarReplacements convertToArithmeticVarReplacements() {
        Map<Variable, Expression> replacements = new HashMap<>();
        for (Variable v : assignments.keySet()) {
            List<Expression> assignementsForVar = assignments.getOrDefault(v, new ArrayList<>());
            if (assignementsForVar.size() == 1) {
                Expression replacement = assignementsForVar.get(0);
                if (!(replacement instanceof NumericBooleanExpression)) {
                    replacements.put(v, replacement);
                    if (eventuallyPrune.get(v).size() != 1) {
                        throw new AssignmentCollectionException("Expected exactly one expressions in pruning.");
                    }
                    continue;
                }
            }
            eventuallyPrune.remove(v);
        }
        boolean changed;
        ArithmeticVarReplacements ret = new ArithmeticVarReplacements(replacements);
        do {
            changed = false;
            for (Variable v : replacements.keySet()) {
                Expression replacement = replacements.get(v);
                if (replacement instanceof Variable && replacements.keySet().contains(replacement)) {
                    replacements.put(v, replacements.get(replacement));
                    changed = true;
                }
                Expression transformedReplacement = ExpressionUtil.transformVars(replacement, ret);
                if(!replacement.equals(transformedReplacement)){
                    replacements.put(v, transformedReplacement);
                    changed = true;
                }
            }
            ret = new ArithmeticVarReplacements(replacements);
        } while (changed);
        return ret;
    }

    public List<Expression> getToPrune() {
        List<Expression> toBePruned = new ArrayList<Expression>();
        for (List<Expression> v : eventuallyPrune.values()) {
            toBePruned.addAll(v);
        }
        return toBePruned;
    }

    public void enterNegation() {
        ++this.insideNegation;
    }

    public void exitNegation() {
        --this.insideNegation;
    }

    public boolean isNegation() {
        return this.insideNegation > 0;
    }

}
