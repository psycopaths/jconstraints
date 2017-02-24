package gov.nasa.jpf.constraints.expressions;

public interface ExpressionOperator {
    public static ExpressionOperator fromString(String str) {
        ExpressionOperator convertedOperator = BitvectorOperator.fromString(str);
        if (convertedOperator == null) {
            convertedOperator = LogicalOperator.fromString(str);
        }
        if (convertedOperator == null) {
            convertedOperator = NumericComparator.fromString(str);
        }
        if (convertedOperator == null) {
            convertedOperator = NumericOperator.fromString(str);
        }
        return convertedOperator;
    }
}
