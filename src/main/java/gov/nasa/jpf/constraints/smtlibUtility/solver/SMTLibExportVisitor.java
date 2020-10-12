package gov.nasa.jpf.constraints.smtlibUtility.solver;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;

public class SMTLibExportVisitor extends AbstractExpressionVisitor<Void, Void> {


    private SMTLibExportGenContext ctx;

    public SMTLibExportVisitor(SMTLibExportGenContext ctx) {
        this.ctx = ctx;
    }

    public void transform(Expression<?> e) {
        defaultVisit(e, null);
    }

    @Override
    public <E> Void visit(Variable<E> var, Void v) {
        ctx.appendVar(var);
        return null;
    }

    @Override
    public <E> Void visit(Constant<E> c, Void v) {
        if (BuiltinTypes.SINT32.equals(c.getType())) {
            Integer i = (Integer) c.getValue();
            ctx.append("#x" + String.format("%1$08x", i));
        }
        else {
            throw new IllegalArgumentException("Unsupported const type: " + c.getType());
        }
        return null;
    }

    @Override
    public Void visit(Negation n, Void v) {
        ctx.open("not");
        visit(n.getNegated(), v);
        ctx.close();
        return null;
    }

    @Override
    public Void visit(NumericBooleanExpression n, Void v) {
        ctx.open( numComp( n.getComparator() ) );
        visit(n.getLeft(), v);
        visit(n.getRight(), v);
        ctx.close();
        return null;
    }

    private String numComp(NumericComparator nc) {
        switch (nc) {
            case EQ: return "=";
            case NE: return "!=";
            case GE: return "bvsge";
            case LE: return "bvsle";
            case GT: return "bvsgt";
            case LT: return "bvslt";
            default:
                throw new IllegalArgumentException("Unsupported: " + nc);
        }
    }

    @Override
    public Void visit(RegExBooleanExpression n, Void data) {
        return null;
    }

    @Override
    public Void visit(StringBooleanExpression n, Void data) {
        return null;
    }

    @Override
    public Void visit(StringIntegerExpression stringIntegerExpression, Void data) {
        return null;
    }

    @Override
    public Void visit(StringCompoundExpression stringCompoundExpression, Void data) {
        return null;
    }

    @Override
    public Void visit(RegexCompoundExpression n, Void data) {
        return null;
    }

    @Override
    public Void visit(RegexOperatorExpression n, Void data) {
        return null;
    }

    @Override
    public <F, E> Void visit(CastExpression<F, E> cast, Void data) {
        return null;
    }

    @Override
    public <E> Void visit(NumericCompound<E> n, Void v) {
        ctx.open( numOp( n.getOperator() ));
        visit(n.getLeft(), v);
        visit(n.getRight(), v);
        ctx.close();
        return null;
    }

    private String numOp(NumericOperator op) {
        switch (op) {
            case DIV: return "bvdiv";
            case MINUS: return "bvsub";
            case MUL: return "bvmul";
            case PLUS: return "bvadd";
            case REM: return "bvrem";
            default:
                throw new IllegalArgumentException("Unsupported: " + op);
        }
    }

    @Override
    public Void visit(PropositionalCompound n, Void data) {
        return null;
    }

    @Override
    public <E> Void visit(IfThenElse<E> n, Void v) {
        ctx.open("ite");
        visit(n.getIf(), v);
        visit(n.getThen(), v);
        visit(n.getElse(), v);
        ctx.close();
        return null;
    }

    @Override
    public <E> Void visit(UnaryMinus<E> n, Void data) {
        return null;
    }

    @Override
    public <E> Void visit(BitvectorExpression<E> bv, Void data) {
        return null;
    }

    @Override
    public <E> Void visit(BitvectorNegation<E> n, Void data) {
        return null;
    }

    @Override
    public Void visit(QuantifierExpression q, Void data) {
        return null;
    }

    @Override
    public <E> Void visit(FunctionExpression<E> f, Void data) {
        return null;
    }

    @Override
    public Void visit(BooleanExpression booleanExpression, Void data) {
        return null;
    }

    @Override
    public Void visit(LetExpression letExpression, Void data) {
        return null;
    }

    @Override
    protected <E> Void defaultVisit(Expression<E> expression, Void v) {
        visit(expression, v);
        return null;
    }
}
