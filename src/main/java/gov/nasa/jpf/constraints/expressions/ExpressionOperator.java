package gov.nasa.jpf.constraints.expressions;

public interface ExpressionOperator {
    public static ExpressionOperator fromString(String str) {
    	System.out.println("In ExpressionOperator: str= " + str);
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
        if (convertedOperator == null) {
        	convertedOperator = StringOperator.fromString(str);
        }
        if (convertedOperator == null) {
        	convertedOperator = StringBooleanOperator.fromString(str);
        }
        if (convertedOperator == null) {
        	convertedOperator = StringIntegerOperator.fromString(str);
        }
        if (convertedOperator == null) {
        	convertedOperator = RegExOperator.fromString(str);
        }
        if (convertedOperator == null) {
        	convertedOperator = RegExCompoundOperator.fromString(str);
        }
        if (convertedOperator == null) {
        	throw new UnsupportedOperationException("String " + str + " cannot be resolved to jConstraintsOperator");
        }
        System.out.println("ConvertedOperator Class: " + convertedOperator.getClass());
        return convertedOperator;
    }
}
