package dk.brics.automaton;

import gov.nasa.jpf.constraints.expressions.AbstractRegExExpression;
import gov.nasa.jpf.constraints.expressions.RegexCompoundExpression;
import gov.nasa.jpf.constraints.expressions.RegexOperatorExpression;

public class RegExpConverter extends RegExp {
	public RegExpConverter(String s) throws IllegalArgumentException {
		super(s);
	}

	public RegExpConverter(String s, int syntax_flags) throws IllegalArgumentException {
		super(s, syntax_flags);
	}

	public static AbstractRegExExpression toSMTExpression(String pattern) {
		RegExpConverter conv =
				new RegExpConverter(pattern.replace("\\d", "[0-9]").replace("\\p{javaWhitespace}", "[ \\t\\n\\x0B\\f\\r]"));
		return convert(conv);
	}

	private static AbstractRegExExpression convert(RegExp conv) {
		switch (conv.kind) {
			case REGEXP_CHAR:
				return convertChar(conv);
			case REGEXP_EMPTY:
				return convertEmpty(conv);
			case REGEXP_UNION:
				return convertUnion(conv);
			case REGEXP_REPEAT:
				return convRepeat(conv);
			case REGEXP_STRING:
				return convString(conv);
			case REGEXP_ANYCHAR:
				return convertAnyChar(conv);
			case REGEXP_INTERVAL:
				return convertInterval(conv);
			case REGEXP_OPTIONAL:
				return convertOptional(conv);
			case REGEXP_ANYSTRING:
				return convertAnyString(conv);
			case REGEXP_CHAR_RANGE:
				return convertCharRange(conv);
			case REGEXP_COMPLEMENT:
				return convertComplement(conv);
			case REGEXP_REPEAT_MIN:
				return convertRepeatMin(conv);
			case REGEXP_INTERSECTION:
				return convertIntersection(conv);
			case REGEXP_CONCATENATION:
				return convertConcatenation(conv);
			case REGEXP_REPEAT_MINMAX:
				return convertRepeatMinMax(conv);
			case REGEXP_AUTOMATON:
			default:
				throw new UnsupportedOperationException();
		}
	}

	private static AbstractRegExExpression convertRepeatMinMax(RegExp conv) {
		throw new UnsupportedOperationException();
	}

	private static AbstractRegExExpression convertConcatenation(RegExp conv) {
		AbstractRegExExpression left = convert(conv.exp1);
		AbstractRegExExpression right = convert(conv.exp2);
		return RegexCompoundExpression.createConcat(left, right);
	}

	private static AbstractRegExExpression convertIntersection(RegExp conv) {
		AbstractRegExExpression left = convert(conv.exp1);
		AbstractRegExExpression right = convert(conv.exp2);
		return RegexCompoundExpression.createIntersection(left, right);
	}

	private static AbstractRegExExpression convertRepeatMin(RegExp conv) {
		return RegexOperatorExpression.createKleenePlus(convert(conv.exp1));
	}

	private static AbstractRegExExpression convertComplement(RegExp conv) {
		return RegexOperatorExpression.createComplement(convert(conv.exp1));
	}

	private static AbstractRegExExpression convertCharRange(RegExp conv) {
		return RegexOperatorExpression.createRange(conv.from, conv.to);
	}

	private static AbstractRegExExpression convertAnyString(RegExp conv) {
		return RegexOperatorExpression.createAll();
	}

	private static AbstractRegExExpression convertOptional(RegExp conv) {
		return RegexOperatorExpression.createOptional(convert(conv.exp1));
	}

	private static AbstractRegExExpression convertInterval(RegExp conv) {
		throw new UnsupportedOperationException();
	}

	private static AbstractRegExExpression convertAnyChar(RegExp conv) {
		return RegexOperatorExpression.createAllChar();
	}

	private static AbstractRegExExpression convString(RegExp conv) {
		return RegexOperatorExpression.createStrToRe(conv.s);
	}

	private static AbstractRegExExpression convRepeat(RegExp conv) {
		return RegexOperatorExpression.createKleeneStar(convert(conv.exp1));
	}

	private static AbstractRegExExpression convertUnion(RegExp conv) {
		AbstractRegExExpression left = convert(conv.exp1);
		AbstractRegExExpression right = convert(conv.exp2);
		return RegexCompoundExpression.createUnion(left, right);
	}

	private static AbstractRegExExpression convertEmpty(RegExp conv) {
		return RegexOperatorExpression.createNoChar();
	}

	private static AbstractRegExExpression convertChar(RegExp conv) {
		String value = new String(new char[]{conv.c});
		return RegexOperatorExpression.createStrToRe(value);
	}
}
