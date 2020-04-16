package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class ExprBinaryTranslator
{
    final ExprTranslator exprTranslator;
    final Alloy2SmtTranslator translator;

    public ExprBinaryTranslator(ExprTranslator exprTranslator)
    {
        this.exprTranslator = exprTranslator;
        translator = exprTranslator.translator;
    }

    SmtExpr translateExprBinary(ExprBinary expr, Environment environment)
    {
        switch (expr.op)
        {
            case ARROW:
                return translateArrow(expr, environment);
            case ANY_ARROW_SOME:
                return translateAnyArrowSome(expr, environment);
            case ANY_ARROW_ONE:
                return translateAnyArrowOne(expr, environment);
            case ANY_ARROW_LONE:
                return translateAnyArrowLone(expr, environment);
            case SOME_ARROW_ANY:
                return translateSomeArrowAny(expr, environment);
            case SOME_ARROW_SOME:
                return translateSomeArrowSome(expr, environment);
            case SOME_ARROW_ONE:
                return translateSomeArrowOne(expr, environment);
            case SOME_ARROW_LONE:
                return translateSomeArrowLone(expr, environment);
            case ONE_ARROW_ANY:
                return translateOneArrowAny(expr, environment);
            case ONE_ARROW_SOME:
                return translateOneArrowSome(expr, environment);
            case ONE_ARROW_ONE:
                return translateOneArrowOne(expr, environment);
            case ONE_ARROW_LONE:
                return translateOneArrowLone(expr, environment);
            case LONE_ARROW_ANY:
                return translateLoneArrowAny(expr, environment);
            case LONE_ARROW_SOME:
                return translateLoneArrowSome(expr, environment);
            case LONE_ARROW_ONE:
                return translateLoneArrowOne(expr, environment);
            case LONE_ARROW_LONE:
                return translateLoneArrowLone(expr, environment);
            case ISSEQ_ARROW_LONE:
                throw new UnsupportedOperationException();

                // Relational operators
            case JOIN:
                return translateJoin(expr, environment);
            case DOMAIN:
                return translateDomainRestriction(expr, environment);
            case RANGE:
                return translateRangeRestriction(expr, environment);
            case INTERSECT:
                return translateSetOperation(expr, SmtBinaryExpr.Op.INTERSECTION, environment);
            case PLUSPLUS:
                return translatePlusPlus(expr, environment);
            case EQUALS:
                return translateEqComparison(expr, SmtBinaryExpr.Op.EQ, environment);
            case NOT_EQUALS:
                return SmtUnaryExpr.Op.NOT.make(translateEqComparison(expr, SmtBinaryExpr.Op.EQ, environment));

            // Set op
            case PLUS:
                return translateSetOperation(expr, SmtBinaryExpr.Op.UNION, environment);
            case MINUS:
                return translateSetOperation(expr, SmtBinaryExpr.Op.SETMINUS, environment);

            // Arithmetic operators            
            case IPLUS:
                return translateArithmetic(expr, SmtBinaryExpr.Op.PLUS, environment);
            case IMINUS:
                return translateArithmetic(expr, SmtBinaryExpr.Op.MINUS, environment);
            case MUL:
                return translateArithmetic(expr, SmtBinaryExpr.Op.MULTIPLY, environment);
            case DIV:
                return translateArithmetic(expr, SmtBinaryExpr.Op.DIVIDE, environment);
            case REM:
                return translateArithmetic(expr, SmtBinaryExpr.Op.MOD, environment);
            // Comparison operators
            case LT:
                return translateComparison(expr, SmtBinaryExpr.Op.LT, environment);
            case LTE:
                return translateComparison(expr, SmtBinaryExpr.Op.LTE, environment);
            case GT:
                return translateComparison(expr, SmtBinaryExpr.Op.GT, environment);
            case GTE:
                return translateComparison(expr, SmtBinaryExpr.Op.GTE, environment);
            case IN:
                return translateSubsetOperation(expr, environment);
            case NOT_IN:
                return SmtUnaryExpr.Op.NOT.make(translateSubsetOperation(expr, environment));
            case IMPLIES:
                return translateImplies(expr, environment);
            case AND:
                return translateAnd(expr, environment);
            case OR:
                return translateOr(expr, environment);
            case IFF:
                return translateEqComparison(expr, SmtBinaryExpr.Op.EQ, environment);
            case NOT_LT:
                return translateComparison(expr, SmtBinaryExpr.Op.GTE, environment);
            case NOT_LTE:
                return translateComparison(expr, SmtBinaryExpr.Op.GT, environment);
            case NOT_GT:
                return translateComparison(expr, SmtBinaryExpr.Op.LTE, environment);
            case NOT_GTE:
                return translateComparison(expr, SmtBinaryExpr.Op.LT, environment);
            case SHL:
                throw new UnsupportedOperationException();
            case SHA:
                throw new UnsupportedOperationException();
            case SHR:
                throw new UnsupportedOperationException();
            default:
                throw new UnsupportedOperationException();
        }
    }

    private SmtExpr translateOneArrowOne(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        SmtVariable multiplicitySet = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);

        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);

        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        SmtVariable x = new SmtVariable("x", ASort.elementSort, false);
        SmtVariable y = new SmtVariable("y", BSort.elementSort, false);
        SmtExpr xMemberA = SmtBinaryExpr.Op.MEMBER.make(x.getVariable(), A);
        SmtExpr yMemberB = SmtBinaryExpr.Op.MEMBER.make(y.getVariable(), B);

        SmtVariable u = new SmtVariable("u", ASort.elementSort, false);
        SmtVariable v = new SmtVariable("v", BSort.elementSort, false);
        SmtExpr uMemberA = SmtBinaryExpr.Op.MEMBER.make(u.getVariable(), A);
        SmtExpr vMemberB = SmtBinaryExpr.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A one -> one B
        // and
        // forall x in A . exists y in B . xy in multiplicitySet and
        //       forall v in B. v != y implies xv not in  multiplicitySet
        // and
        // forall y in B . exists x in A . xy in multiplicitySet and
        //       forall u in A. u != x implies uy not in  multiplicitySet

        SmtExpr xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        SmtExpr xvTuple = getTupleConcatenation(ASort, BSort, x, v);
        SmtExpr uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        SmtExpr xvMember = SmtBinaryExpr.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());
        SmtExpr uyMember = SmtBinaryExpr.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        SmtExpr notXV = SmtUnaryExpr.Op.NOT.make(xvMember);
        SmtExpr notUY = SmtUnaryExpr.Op.NOT.make(uyMember);

        SmtExpr vEqualY = SmtBinaryExpr.Op.EQ.make(v.getVariable(), y.getVariable());
        SmtExpr notVEqualY = SmtUnaryExpr.Op.NOT.make(vEqualY);

        SmtExpr vImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(vMemberB, notVEqualY), notXV);
        SmtExpr forAllV = SmtQtExpr.Op.FORALL.make(vImplies, v);

        SmtExpr uEqualX = SmtBinaryExpr.Op.EQ.make(u.getVariable(), x.getVariable());
        SmtExpr notUEqualX = SmtUnaryExpr.Op.NOT.make(uEqualX);

        SmtExpr uImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(uMemberA, notUEqualX), notUY);
        SmtExpr forAllU = SmtQtExpr.Op.FORALL.make(uImplies, u);

        SmtExpr existsYBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(yMemberB, xyMember), forAllV);

        SmtExpr existsY = SmtQtExpr.Op.EXISTS.make(existsYBody, y);
        SmtExpr xImplies = SmtBinaryExpr.Op.IMPLIES.make(xMemberA, existsY);
        SmtExpr forAllX = SmtQtExpr.Op.FORALL.make(xImplies, x);


        SmtExpr existsXBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(xMemberA, xyMember), forAllU);

        SmtExpr existsX = SmtQtExpr.Op.EXISTS.make(existsXBody, x);
        SmtExpr yImplies = SmtBinaryExpr.Op.IMPLIES.make(yMemberB, existsX);
        SmtExpr forAllY = SmtQtExpr.Op.FORALL.make(yImplies, y);


        SmtExpr and = SmtMultiArityExpr.Op.AND.make(subset, forAllX, forAllY);
        SmtQtExpr existsSet = SmtQtExpr.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);


        return multiplicitySet.getVariable();
    }

    private SmtExpr translateOneArrowSome(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        SmtVariable multiplicitySet = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);


        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);

        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        SmtVariable x = new SmtVariable("x", ASort.elementSort, false);
        SmtVariable y = new SmtVariable("y", BSort.elementSort, false);
        SmtExpr xMemberA = SmtBinaryExpr.Op.MEMBER.make(x.getVariable(), A);
        SmtExpr yMemberB = SmtBinaryExpr.Op.MEMBER.make(y.getVariable(), B);

        SmtVariable u = new SmtVariable("u", ASort.elementSort, false);
        SmtExpr uMemberA = SmtBinaryExpr.Op.MEMBER.make(u.getVariable(), A);

        // multiplicitySet subset of A one -> some B
        // and
        // forall x in A . exists y in B . xy in multiplicitySet
        // and
        // forall y in B . exists x in A . xy in multiplicitySet and
        //       forall u in A. u != x implies uy not in  multiplicitySet

        SmtExpr xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        SmtExpr uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());

        SmtExpr uyMember = SmtBinaryExpr.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        SmtExpr notUY = SmtUnaryExpr.Op.NOT.make(uyMember);

        SmtExpr uEqualX = SmtBinaryExpr.Op.EQ.make(u.getVariable(), x.getVariable());
        SmtExpr notUEqualX = SmtUnaryExpr.Op.NOT.make(uEqualX);

        SmtExpr uImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(uMemberA, notUEqualX), notUY);
        SmtExpr forAllU = SmtQtExpr.Op.FORALL.make(uImplies, u);

        SmtExpr existsYBody = SmtMultiArityExpr.Op.AND.make(yMemberB, xyMember);

        SmtExpr existsY = SmtQtExpr.Op.EXISTS.make(existsYBody, y);
        SmtExpr xImplies = SmtBinaryExpr.Op.IMPLIES.make(xMemberA, existsY);
        SmtExpr forAllX = SmtQtExpr.Op.FORALL.make(xImplies, x);

        SmtExpr existsXBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(xMemberA, xyMember), forAllU);

        SmtExpr existsX = SmtQtExpr.Op.EXISTS.make(existsXBody, x);
        SmtExpr yImplies = SmtBinaryExpr.Op.IMPLIES.make(yMemberB, existsX);
        SmtExpr forAllY = SmtQtExpr.Op.FORALL.make(yImplies, y);

        SmtExpr and = SmtMultiArityExpr.Op.AND.make(subset, forAllX, forAllY);
        SmtQtExpr existsSet = SmtQtExpr.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);


        return multiplicitySet.getVariable();
    }

    private SmtExpr translateOneArrowAny(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        SmtVariable multiplicitySet = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);

        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);

        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        SmtVariable x = new SmtVariable("x", ASort.elementSort, false);
        SmtVariable y = new SmtVariable("y", BSort.elementSort, false);
        SmtExpr xMemberA = SmtBinaryExpr.Op.MEMBER.make(x.getVariable(), A);
        SmtExpr yMemberB = SmtBinaryExpr.Op.MEMBER.make(y.getVariable(), B);

        SmtVariable u = new SmtVariable("u", ASort.elementSort, false);
        SmtExpr uMemberA = SmtBinaryExpr.Op.MEMBER.make(u.getVariable(), A);

        // multiplicitySet subset of A one -> set B
        // and
        // forall y in B . exists x in A . xy in multiplicitySet and
        //       forall u in A. u != x implies uy not in  multiplicitySet

        SmtExpr xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        SmtExpr uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());

        SmtExpr uyMember = SmtBinaryExpr.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        SmtExpr notUY = SmtUnaryExpr.Op.NOT.make(uyMember);

        SmtExpr uEqualX = SmtBinaryExpr.Op.EQ.make(u.getVariable(), x.getVariable());
        SmtExpr notUEqualX = SmtUnaryExpr.Op.NOT.make(uEqualX);

        SmtExpr uImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(uMemberA, notUEqualX), notUY);
        SmtExpr forAllU = SmtQtExpr.Op.FORALL.make(uImplies, u);

        SmtExpr existsXBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(xMemberA, xyMember), forAllU);

        SmtExpr existsX = SmtQtExpr.Op.EXISTS.make(existsXBody, x);
        SmtExpr yImplies = SmtBinaryExpr.Op.IMPLIES.make(yMemberB, existsX);
        SmtExpr forAllY = SmtQtExpr.Op.FORALL.make(yImplies, y);

        SmtExpr and = SmtMultiArityExpr.Op.AND.make(subset, forAllY);

        SmtQtExpr existsSet = SmtQtExpr.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);

        return multiplicitySet.getVariable();
    }

    private SmtExpr translateSomeArrowOne(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        SmtVariable multiplicitySet = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);

        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);

        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        SmtVariable x = new SmtVariable("x", ASort.elementSort, false);
        SmtVariable y = new SmtVariable("y", BSort.elementSort, false);
        SmtExpr xMemberA = SmtBinaryExpr.Op.MEMBER.make(x.getVariable(), A);
        SmtExpr yMemberB = SmtBinaryExpr.Op.MEMBER.make(y.getVariable(), B);

        SmtVariable v = new SmtVariable("v", BSort.elementSort, false);
        SmtExpr vMemberB = SmtBinaryExpr.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A some -> one B
        // and
        // forall x in A . exists y in B . xy in multiplicitySet and
        //       forall v in B. v != y implies xv not in  multiplicitySet
        // and
        // forall y in B . exists x in A . xy in multiplicitySet

        SmtExpr xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        SmtExpr xvTuple = getTupleConcatenation(ASort, BSort, x, v);

        SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        SmtExpr xvMember = SmtBinaryExpr.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());

        SmtExpr notXV = SmtUnaryExpr.Op.NOT.make(xvMember);

        SmtExpr vEqualY = SmtBinaryExpr.Op.EQ.make(v.getVariable(), y.getVariable());
        SmtExpr notVEqualY = SmtUnaryExpr.Op.NOT.make(vEqualY);

        SmtExpr vImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(vMemberB, notVEqualY), notXV);
        SmtExpr forAllV = SmtQtExpr.Op.FORALL.make(vImplies, v);

        SmtExpr existsYBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(yMemberB, xyMember), forAllV);

        SmtExpr existsY = SmtQtExpr.Op.EXISTS.make(existsYBody, y);
        SmtExpr xImplies = SmtBinaryExpr.Op.IMPLIES.make(xMemberA, existsY);
        SmtExpr forAllX = SmtQtExpr.Op.FORALL.make(xImplies, x);


        SmtExpr existsXBody = SmtMultiArityExpr.Op.AND.make(xMemberA, xyMember);

        SmtExpr existsX = SmtQtExpr.Op.EXISTS.make(existsXBody, x);
        SmtExpr yImplies = SmtBinaryExpr.Op.IMPLIES.make(yMemberB, existsX);
        SmtExpr forAllY = SmtQtExpr.Op.FORALL.make(yImplies, y);

        SmtExpr and = SmtMultiArityExpr.Op.AND.make(subset, forAllX, forAllY);
        SmtQtExpr existsSet = SmtQtExpr.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);

        return multiplicitySet.getVariable();
    }

    private SmtExpr translateAnyArrowOne(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        SmtVariable multiplicitySet = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);

        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);

        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        SmtVariable x = new SmtVariable("x", ASort.elementSort, false);
        SmtVariable y = new SmtVariable("y", BSort.elementSort, false);
        SmtExpr xMemberA = SmtBinaryExpr.Op.MEMBER.make(x.getVariable(), A);
        SmtExpr yMemberB = SmtBinaryExpr.Op.MEMBER.make(y.getVariable(), B);

        SmtVariable v = new SmtVariable("v", BSort.elementSort, false);
        SmtExpr vMemberB = SmtBinaryExpr.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A set -> one B
        // and
        // forall x in A . exists y in B . xy in multiplicitySet and
        //       forall v in B. v != y implies xv not in  multiplicitySet

        SmtExpr xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        SmtExpr xvTuple = getTupleConcatenation(ASort, BSort, x, v);

        SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        SmtExpr xvMember = SmtBinaryExpr.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());

        SmtExpr notXV = SmtUnaryExpr.Op.NOT.make(xvMember);

        SmtExpr vEqualY = SmtBinaryExpr.Op.EQ.make(v.getVariable(), y.getVariable());
        SmtExpr notVEqualY = SmtUnaryExpr.Op.NOT.make(vEqualY);

        SmtExpr vImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(vMemberB, notVEqualY), notXV);
        SmtExpr forAllV = SmtQtExpr.Op.FORALL.make(vImplies, v);

        SmtExpr existsYBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(yMemberB, xyMember), forAllV);

        SmtExpr existsY = SmtQtExpr.Op.EXISTS.make(existsYBody, y);
        SmtExpr xImplies = SmtBinaryExpr.Op.IMPLIES.make(xMemberA, existsY);
        SmtExpr forAllX = SmtQtExpr.Op.FORALL.make(xImplies, x);

        SmtExpr and = SmtMultiArityExpr.Op.AND.make(subset, forAllX);
        SmtQtExpr existsSet = SmtQtExpr.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);

        return multiplicitySet.getVariable();
    }

    private SmtExpr translateSomeArrowSome(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        SmtVariable multiplicitySet = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);

        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);

        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        SmtVariable x = new SmtVariable("x", ASort.elementSort, false);
        SmtVariable y = new SmtVariable("y", BSort.elementSort, false);
        SmtExpr xMemberA = SmtBinaryExpr.Op.MEMBER.make(x.getVariable(), A);
        SmtExpr yMemberB = SmtBinaryExpr.Op.MEMBER.make(y.getVariable(), B);

        // multiplicitySet subset of A some -> some B
        // and
        // forall x in A . exists y in B . xy in multiplicitySet
        // and
        // forall y in B . exists x in A . xy in multiplicitySet

        SmtExpr xyTuple = getTupleConcatenation(ASort, BSort, x, y);

        SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());

        SmtExpr existsYBody = SmtMultiArityExpr.Op.AND.make(yMemberB, xyMember);
        SmtExpr existsY = SmtQtExpr.Op.EXISTS.make(existsYBody, y);
        SmtExpr xImplies = SmtBinaryExpr.Op.IMPLIES.make(xMemberA, existsY);
        SmtExpr forAllX = SmtQtExpr.Op.FORALL.make(xImplies, x);

        SmtExpr existsXBody = SmtMultiArityExpr.Op.AND.make(xMemberA, xyMember);

        SmtExpr existsX = SmtQtExpr.Op.EXISTS.make(existsXBody, x);
        SmtExpr yImplies = SmtBinaryExpr.Op.IMPLIES.make(yMemberB, existsX);
        SmtExpr forAllY = SmtQtExpr.Op.FORALL.make(yImplies, y);

        SmtExpr and = SmtMultiArityExpr.Op.AND.make(Arrays.asList(forAllX, forAllY, subset));

        SmtQtExpr existsSet = SmtQtExpr.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);
        return multiplicitySet.getVariable();
    }

    private SmtExpr translateSomeArrowAny(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        SmtVariable multiplicitySet = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);

        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);

        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        SmtVariable x = new SmtVariable("x", ASort.elementSort, false);
        SmtVariable y = new SmtVariable("y", BSort.elementSort, false);
        SmtExpr xMemberA = SmtBinaryExpr.Op.MEMBER.make(x.getVariable(), A);
        SmtExpr yMemberB = SmtBinaryExpr.Op.MEMBER.make(y.getVariable(), B);

        // multiplicitySet subset of A some -> set B
        // and
        // forall y in B . exists x in A . xy in multiplicitySet

        SmtExpr xyTuple = getTupleConcatenation(ASort, BSort, x, y);

        SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());

        SmtExpr existsXBody = SmtMultiArityExpr.Op.AND.make(xMemberA, xyMember);
        SmtExpr existsX = SmtQtExpr.Op.EXISTS.make(existsXBody, x);
        SmtExpr yImplies = SmtBinaryExpr.Op.IMPLIES.make(yMemberB, existsX);
        SmtExpr forAllY = SmtQtExpr.Op.FORALL.make(yImplies, y);

        SmtExpr and = SmtMultiArityExpr.Op.AND.make(subset, forAllY);
        SmtQtExpr existsSet = SmtQtExpr.Op.EXISTS.make(and, multiplicitySet);

        environment.addAuxiliaryFormula(existsSet);

        return multiplicitySet.getVariable();
    }

    private SmtExpr translateAnyArrowSome(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        SmtVariable multiplicitySet = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);

        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);

        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        SmtVariable x = new SmtVariable("x", ASort.elementSort, false);
        SmtVariable y = new SmtVariable("y", BSort.elementSort, false);
        SmtExpr xMemberA = SmtBinaryExpr.Op.MEMBER.make(x.getVariable(), A);
        SmtExpr yMemberB = SmtBinaryExpr.Op.MEMBER.make(y.getVariable(), B);

        // multiplicitySet subset of A set -> some B
        // and
        // forall x in A . exists y in B . xy in multiplicitySet

        SmtExpr xyTuple = getTupleConcatenation(ASort, BSort, x, y);

        SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());

        SmtExpr existsYBody = SmtMultiArityExpr.Op.AND.make(yMemberB, xyMember);
        SmtExpr existsY = SmtQtExpr.Op.EXISTS.make(existsYBody, y);
        SmtExpr xImplies = SmtBinaryExpr.Op.IMPLIES.make(xMemberA, existsY);
        SmtExpr forAllX = SmtQtExpr.Op.FORALL.make(xImplies, x);
        SmtExpr and = SmtMultiArityExpr.Op.AND.make(subset, forAllX);
        SmtQtExpr existsSet = SmtQtExpr.Op.EXISTS.make(and, multiplicitySet);

        environment.addAuxiliaryFormula(existsSet);
        return multiplicitySet.getVariable();
    }

    private SmtExpr translateOneArrowLone(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        SmtVariable multiplicitySet = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);


        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);

        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        SmtVariable x = new SmtVariable("x", ASort.elementSort, false);
        SmtVariable y = new SmtVariable("y", BSort.elementSort, false);
        SmtExpr xMemberA = SmtBinaryExpr.Op.MEMBER.make(x.getVariable(), A);
        SmtExpr yMemberB = SmtBinaryExpr.Op.MEMBER.make(y.getVariable(), B);

        SmtVariable u = new SmtVariable("u", ASort.elementSort, false);
        SmtVariable v = new SmtVariable("v", BSort.elementSort, false);
        SmtExpr uMemberA = SmtBinaryExpr.Op.MEMBER.make(u.getVariable(), A);
        SmtExpr vMemberB = SmtBinaryExpr.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A one -> lone B
        // and
        // forall x in A .
        //      (forall y in B. xy not in multiplicitySet)
        //      or
        //      (exists y in B . xy in multiplicitySet and
        //          forall v in B. v != y implies xv not in  multiplicitySet)
        // and
        // forall y in B . exists x in A . xy in multiplicitySet and
        //       forall u in A. u != x implies uy not in  multiplicitySet


        SmtExpr xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        SmtExpr xvTuple = getTupleConcatenation(ASort, BSort, x, v);
        SmtExpr uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        SmtExpr xvMember = SmtBinaryExpr.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());
        SmtExpr uyMember = SmtBinaryExpr.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        SmtExpr notXY = SmtUnaryExpr.Op.NOT.make(xyMember);
        SmtExpr notXV = SmtUnaryExpr.Op.NOT.make(xvMember);
        SmtExpr notUY = SmtUnaryExpr.Op.NOT.make(uyMember);

        SmtExpr vEqualY = SmtBinaryExpr.Op.EQ.make(v.getVariable(), y.getVariable());
        SmtExpr notVEqualY = SmtUnaryExpr.Op.NOT.make(vEqualY);

        SmtExpr vImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(vMemberB, notVEqualY), notXV);
        SmtExpr forAllV = SmtQtExpr.Op.FORALL.make(vImplies, v);

        SmtExpr uEqualX = SmtBinaryExpr.Op.EQ.make(u.getVariable(), x.getVariable());
        SmtExpr notUEqualX = SmtUnaryExpr.Op.NOT.make(uEqualX);

        SmtExpr uImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(uMemberA, notUEqualX), notUY);
        SmtExpr forAllU = SmtQtExpr.Op.FORALL.make(uImplies, u);

        SmtExpr existsYBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(yMemberB, xyMember), forAllV);

        SmtExpr existsY = SmtQtExpr.Op.EXISTS.make(existsYBody, y);
        SmtExpr lone = SmtMultiArityExpr.Op.OR.make(SmtQtExpr.Op.FORALL.make(notXY, y), existsY);
        SmtExpr xImplies = SmtBinaryExpr.Op.IMPLIES.make(xMemberA, lone);
        SmtExpr forAllX = SmtQtExpr.Op.FORALL.make(xImplies, x);

        SmtExpr existsXBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(xMemberA, xyMember), forAllU);

        SmtExpr existsX = SmtQtExpr.Op.EXISTS.make(existsXBody, x);
        SmtExpr yImplies = SmtBinaryExpr.Op.IMPLIES.make(yMemberB, existsX);
        SmtExpr forAllY = SmtQtExpr.Op.FORALL.make(yImplies, y);

        SmtExpr and = SmtMultiArityExpr.Op.AND.make(subset, forAllX, forAllY);
        SmtQtExpr existsSet = SmtQtExpr.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);


        return multiplicitySet.getVariable();
    }

    private SmtExpr translateSomeArrowLone(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        SmtVariable multiplicitySet = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);


        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);

        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(multiplicitySet.getVariable(), product);


        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        SmtVariable x = new SmtVariable("x", ASort.elementSort, false);
        SmtVariable y = new SmtVariable("y", BSort.elementSort, false);
        SmtExpr xMemberA = SmtBinaryExpr.Op.MEMBER.make(x.getVariable(), A);
        SmtExpr yMemberB = SmtBinaryExpr.Op.MEMBER.make(y.getVariable(), B);

        SmtVariable v = new SmtVariable("v", BSort.elementSort, false);
        SmtExpr vMemberB = SmtBinaryExpr.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A some -> lone B
        // and
        // forall x in A .
        //      (forall y in B. xy not in multiplicitySet)
        //      or
        //      (exists y in B . xy in multiplicitySet and
        //          forall v in B. v != y implies xv not in  multiplicitySet)
        // and
        // forall y in B . exists x in A . xy in multiplicitySet

        SmtExpr xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        SmtExpr xvTuple = getTupleConcatenation(ASort, BSort, x, v);

        SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        SmtExpr xvMember = SmtBinaryExpr.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());

        SmtExpr notXY = SmtUnaryExpr.Op.NOT.make(xyMember);
        SmtExpr notXV = SmtUnaryExpr.Op.NOT.make(xvMember);

        SmtExpr vEqualY = SmtBinaryExpr.Op.EQ.make(v.getVariable(), y.getVariable());
        SmtExpr notVEqualY = SmtUnaryExpr.Op.NOT.make(vEqualY);

        SmtExpr vImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(vMemberB, notVEqualY), notXV);
        SmtExpr forAllV = SmtQtExpr.Op.FORALL.make(vImplies, v);

        SmtExpr existsYBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(yMemberB, xyMember), forAllV);

        SmtExpr existsY = SmtQtExpr.Op.EXISTS.make(existsYBody, y);
        SmtExpr lone = SmtMultiArityExpr.Op.OR.make(SmtQtExpr.Op.FORALL.make(notXY, y), existsY);
        SmtExpr xImplies = SmtBinaryExpr.Op.IMPLIES.make(xMemberA, lone);
        SmtExpr forAllX = SmtQtExpr.Op.FORALL.make(xImplies, x);

        SmtExpr existsXBody = SmtMultiArityExpr.Op.AND.make(xMemberA, xyMember);

        SmtExpr existsX = SmtQtExpr.Op.EXISTS.make(existsXBody, x);
        SmtExpr yImplies = SmtBinaryExpr.Op.IMPLIES.make(yMemberB, existsX);
        SmtExpr forAllY = SmtQtExpr.Op.FORALL.make(yImplies, y);

        SmtExpr and = SmtMultiArityExpr.Op.AND.make(subset, forAllX, forAllY);
        SmtQtExpr existsSet = SmtQtExpr.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);

        return multiplicitySet.getVariable();
    }

    private SmtExpr translateAnyArrowLone(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        SmtVariable multiplicitySet = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);

        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);

        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(multiplicitySet.getVariable(), product);


        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        SmtVariable x = new SmtVariable("x", ASort.elementSort, false);
        SmtVariable y = new SmtVariable("y", BSort.elementSort, false);
        SmtExpr xMemberA = SmtBinaryExpr.Op.MEMBER.make(x.getVariable(), A);
        SmtExpr yMemberB = SmtBinaryExpr.Op.MEMBER.make(y.getVariable(), B);

        SmtVariable v = new SmtVariable("v", BSort.elementSort, false);
        SmtExpr vMemberB = SmtBinaryExpr.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A set -> lone B
        // and
        // forall x in A .
        //      (forall y in B. xy not in multiplicitySet)
        //      or
        //      (exists y in B . xy in multiplicitySet and
        //          forall v in B. v != y implies xv not in  multiplicitySet)

        SmtExpr xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        SmtExpr xvTuple = getTupleConcatenation(ASort, BSort, x, v);

        SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        SmtExpr xvMember = SmtBinaryExpr.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());

        SmtExpr notXY = SmtUnaryExpr.Op.NOT.make(xyMember);
        SmtExpr notXV = SmtUnaryExpr.Op.NOT.make(xvMember);

        SmtExpr vEqualY = SmtBinaryExpr.Op.EQ.make(v.getVariable(), y.getVariable());
        SmtExpr notVEqualY = SmtUnaryExpr.Op.NOT.make(vEqualY);

        SmtExpr vImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(vMemberB, notVEqualY), notXV);
        SmtExpr forAllV = SmtQtExpr.Op.FORALL.make(vImplies, v);

        SmtExpr existsYBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(yMemberB, xyMember), forAllV);

        SmtExpr existsY = SmtQtExpr.Op.EXISTS.make(existsYBody, y);
        SmtExpr lone = SmtMultiArityExpr.Op.OR.make(SmtQtExpr.Op.FORALL.make(notXY, y), existsY);
        SmtExpr xImplies = SmtBinaryExpr.Op.IMPLIES.make(xMemberA, lone);
        SmtExpr forAllX = SmtQtExpr.Op.FORALL.make(xImplies, x);

        SmtExpr and = SmtMultiArityExpr.Op.AND.make(subset, forAllX);
        SmtQtExpr existsSet = SmtQtExpr.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);


        return multiplicitySet.getVariable();
    }

    private SmtExpr translateLoneArrowLone(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        SmtVariable multiplicitySet = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);

        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);

        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        SmtVariable x = new SmtVariable("x", ASort.elementSort, false);
        SmtVariable y = new SmtVariable("y", BSort.elementSort, false);
        SmtExpr xMemberA = SmtBinaryExpr.Op.MEMBER.make(x.getVariable(), A);
        SmtExpr yMemberB = SmtBinaryExpr.Op.MEMBER.make(y.getVariable(), B);

        SmtVariable u = new SmtVariable("u", ASort.elementSort, false);
        SmtVariable v = new SmtVariable("v", BSort.elementSort, false);
        SmtExpr uMemberA = SmtBinaryExpr.Op.MEMBER.make(u.getVariable(), A);
        SmtExpr vMemberB = SmtBinaryExpr.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A lone -> lone B
        // and
        // forall x in A .
        //      (forall y in B. xy not in multiplicitySet)
        //      or
        //      (exists y in B . xy in multiplicitySet and
        //          forall v in B. v != y implies xv not in  multiplicitySet)
        // and
        // forall y in B.
        //      (forall x in A. xy not in multiplicitySet)
        //      or
        //      (exists x in A . xy in multiplicitySet and
        //          forall u in A. u != x implies uy not in  multiplicitySet)


        SmtExpr xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        SmtExpr xvTuple = getTupleConcatenation(ASort, BSort, x, v);
        SmtExpr uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        SmtExpr xvMember = SmtBinaryExpr.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());
        SmtExpr uyMember = SmtBinaryExpr.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        SmtExpr notXY = SmtUnaryExpr.Op.NOT.make(xyMember);
        SmtExpr notXV = SmtUnaryExpr.Op.NOT.make(xvMember);
        SmtExpr notUY = SmtUnaryExpr.Op.NOT.make(uyMember);

        SmtExpr vEqualY = SmtBinaryExpr.Op.EQ.make(v.getVariable(), y.getVariable());
        SmtExpr notVEqualY = SmtUnaryExpr.Op.NOT.make(vEqualY);

        SmtExpr vImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(vMemberB, notVEqualY), notXV);
        SmtExpr forAllV = SmtQtExpr.Op.FORALL.make(vImplies, v);

        SmtExpr uEqualX = SmtBinaryExpr.Op.EQ.make(u.getVariable(), x.getVariable());
        SmtExpr notUEqualX = SmtUnaryExpr.Op.NOT.make(uEqualX);

        SmtExpr uImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(uMemberA, notUEqualX), notUY);
        SmtExpr forAllU = SmtQtExpr.Op.FORALL.make(uImplies, u);

        SmtExpr existsYBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(yMemberB, xyMember), forAllV);

        SmtExpr existsY = SmtQtExpr.Op.EXISTS.make(existsYBody, y);
        SmtExpr loneWest = SmtMultiArityExpr.Op.OR.make(SmtQtExpr.Op.FORALL.make(notXY, y), existsY);
        SmtExpr xImplies = SmtBinaryExpr.Op.IMPLIES.make(xMemberA, loneWest);
        SmtExpr forAllX = SmtQtExpr.Op.FORALL.make(xImplies, x);

        SmtExpr existsXBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(xMemberA, xyMember), forAllU);

        SmtExpr existsX = SmtQtExpr.Op.EXISTS.make(existsXBody, x);
        SmtExpr loneEast = SmtMultiArityExpr.Op.OR.make(SmtQtExpr.Op.FORALL.make(notXY, x), existsX);
        SmtExpr yImplies = SmtBinaryExpr.Op.IMPLIES.make(yMemberB, loneEast);
        SmtExpr forAllY = SmtQtExpr.Op.FORALL.make(yImplies, y);

        SmtExpr and = SmtMultiArityExpr.Op.AND.make(subset, forAllX, forAllY);
        SmtQtExpr existsSet = SmtQtExpr.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);


        return multiplicitySet.getVariable();
    }

    private SmtExpr translateLoneArrowOne(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        SmtVariable multiplicitySet = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);

        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);

        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        SmtVariable x = new SmtVariable("x", ASort.elementSort, false);
        SmtVariable y = new SmtVariable("y", BSort.elementSort, false);
        SmtExpr xMemberA = SmtBinaryExpr.Op.MEMBER.make(x.getVariable(), A);
        SmtExpr yMemberB = SmtBinaryExpr.Op.MEMBER.make(y.getVariable(), B);

        SmtVariable u = new SmtVariable("u", ASort.elementSort, false);
        SmtVariable v = new SmtVariable("v", BSort.elementSort, false);
        SmtExpr uMemberA = SmtBinaryExpr.Op.MEMBER.make(u.getVariable(), A);
        SmtExpr vMemberB = SmtBinaryExpr.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A lone -> one B
        // and
        // forall x in A .
        //      (exists y in B . xy in multiplicitySet and
        //          forall v in B. v != y implies xv not in  multiplicitySet)
        // and
        // forall y in B.
        //      (forall x in A. xy not in multiplicitySet)
        //      or
        //      (exists x in A . xy in multiplicitySet and
        //          forall u in A. u != x implies uy not in  multiplicitySet)


        SmtExpr xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        SmtExpr xvTuple = getTupleConcatenation(ASort, BSort, x, v);
        SmtExpr uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        SmtExpr xvMember = SmtBinaryExpr.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());
        SmtExpr uyMember = SmtBinaryExpr.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        SmtExpr notXY = SmtUnaryExpr.Op.NOT.make(xyMember);
        SmtExpr notXV = SmtUnaryExpr.Op.NOT.make(xvMember);
        SmtExpr notUY = SmtUnaryExpr.Op.NOT.make(uyMember);

        SmtExpr vEqualY = SmtBinaryExpr.Op.EQ.make(v.getVariable(), y.getVariable());
        SmtExpr notVEqualY = SmtUnaryExpr.Op.NOT.make(vEqualY);

        SmtExpr vImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(vMemberB, notVEqualY), notXV);
        SmtExpr forAllV = SmtQtExpr.Op.FORALL.make(vImplies, v);

        SmtExpr uEqualX = SmtBinaryExpr.Op.EQ.make(u.getVariable(), x.getVariable());
        SmtExpr notUEqualX = SmtUnaryExpr.Op.NOT.make(uEqualX);

        SmtExpr uImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(uMemberA, notUEqualX), notUY);
        SmtExpr forAllU = SmtQtExpr.Op.FORALL.make(uImplies, u);

        SmtExpr existsYBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(yMemberB, xyMember), forAllV);

        SmtExpr existsY = SmtQtExpr.Op.EXISTS.make(existsYBody, y);
        SmtExpr xImplies = SmtBinaryExpr.Op.IMPLIES.make(xMemberA, existsY);
        SmtExpr forAllX = SmtQtExpr.Op.FORALL.make(xImplies, x);

        SmtExpr existsXBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(xMemberA, xyMember), forAllU);

        SmtExpr existsX = SmtQtExpr.Op.EXISTS.make(existsXBody, x);
        SmtExpr loneEast = SmtMultiArityExpr.Op.OR.make(SmtQtExpr.Op.FORALL.make(notXY, x), existsX);
        SmtExpr yImplies = SmtBinaryExpr.Op.IMPLIES.make(yMemberB, loneEast);
        SmtExpr forAllY = SmtQtExpr.Op.FORALL.make(yImplies, y);

        SmtExpr and = SmtMultiArityExpr.Op.AND.make(subset, forAllX, forAllY);
        SmtQtExpr existsSet = SmtQtExpr.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);


        return multiplicitySet.getVariable();
    }

    private SmtExpr translateLoneArrowSome(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        SmtVariable multiplicitySet = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);

        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);

        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(multiplicitySet.getVariable(), product);


        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        SmtVariable x = new SmtVariable("x", ASort.elementSort, false);
        SmtVariable y = new SmtVariable("y", BSort.elementSort, false);
        SmtExpr xMemberA = SmtBinaryExpr.Op.MEMBER.make(x.getVariable(), A);
        SmtExpr yMemberB = SmtBinaryExpr.Op.MEMBER.make(y.getVariable(), B);

        SmtVariable u = new SmtVariable("u", ASort.elementSort, false);
        SmtExpr uMemberA = SmtBinaryExpr.Op.MEMBER.make(u.getVariable(), A);

        // multiplicitySet subset of A lone -> some B
        // and
        // forall x in A .
        //      (exists y in B . xy in multiplicitySet
        // and
        // forall y in B.
        //      (forall x in A. xy not in multiplicitySet)
        //      or
        //      (exists x in A . xy in multiplicitySet and
        //          forall u in A. u != x implies uy not in  multiplicitySet)


        SmtExpr xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        SmtExpr uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        SmtExpr uyMember = SmtBinaryExpr.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        SmtExpr notXY = SmtUnaryExpr.Op.NOT.make(xyMember);
        SmtExpr notUY = SmtUnaryExpr.Op.NOT.make(uyMember);


        SmtExpr uEqualX = SmtBinaryExpr.Op.EQ.make(u.getVariable(), x.getVariable());
        SmtExpr notUEqualX = SmtUnaryExpr.Op.NOT.make(uEqualX);

        SmtExpr uImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(uMemberA, notUEqualX), notUY);
        SmtExpr forAllU = SmtQtExpr.Op.FORALL.make(uImplies, u);

        SmtExpr existsYBody = SmtMultiArityExpr.Op.AND.make(yMemberB, xyMember);

        SmtExpr existsY = SmtQtExpr.Op.EXISTS.make(existsYBody, y);
        SmtExpr xImplies = SmtBinaryExpr.Op.IMPLIES.make(xMemberA, existsY);
        SmtExpr forAllX = SmtQtExpr.Op.FORALL.make(xImplies, x);


        SmtExpr existsXBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(xMemberA, xyMember), forAllU);

        SmtExpr existsX = SmtQtExpr.Op.EXISTS.make(existsXBody, x);
        SmtExpr loneEast = SmtMultiArityExpr.Op.OR.make(SmtQtExpr.Op.FORALL.make(notXY, x), existsX);
        SmtExpr yImplies = SmtBinaryExpr.Op.IMPLIES.make(yMemberB, loneEast);
        SmtExpr forAllY = SmtQtExpr.Op.FORALL.make(yImplies, y);

        SmtExpr and = SmtMultiArityExpr.Op.AND.make(subset, forAllX, forAllY);
        SmtQtExpr existsSet = SmtQtExpr.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);

        return multiplicitySet.getVariable();
    }

    private SmtExpr translateLoneArrowAny(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        SmtVariable multiplicitySet = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);

        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);

        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        SmtVariable x = new SmtVariable("x", ASort.elementSort, false);
        SmtVariable y = new SmtVariable("y", BSort.elementSort, false);
        SmtExpr xMemberA = SmtBinaryExpr.Op.MEMBER.make(x.getVariable(), A);
        SmtExpr yMemberB = SmtBinaryExpr.Op.MEMBER.make(y.getVariable(), B);

        SmtVariable u = new SmtVariable("u", ASort.elementSort, false);
        SmtExpr uMemberA = SmtBinaryExpr.Op.MEMBER.make(u.getVariable(), A);

        // multiplicitySet subset of A lone -> set B
        // and
        // forall y in B.
        //      (forall x in A. xy not in multiplicitySet)
        //      or
        //      (exists x in A . xy in multiplicitySet and
        //          forall u in A. u != x implies uy not in  multiplicitySet)


        SmtExpr xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        SmtExpr uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        SmtExpr xyMember = SmtBinaryExpr.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        SmtExpr uyMember = SmtBinaryExpr.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        SmtExpr notXY = SmtUnaryExpr.Op.NOT.make(xyMember);
        SmtExpr notUY = SmtUnaryExpr.Op.NOT.make(uyMember);


        SmtExpr uEqualX = SmtBinaryExpr.Op.EQ.make(u.getVariable(), x.getVariable());
        SmtExpr notUEqualX = SmtUnaryExpr.Op.NOT.make(uEqualX);

        SmtExpr uImplies = SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(uMemberA, notUEqualX), notUY);
        SmtExpr forAllU = SmtQtExpr.Op.FORALL.make(uImplies, u);
        SmtExpr existsXBody = SmtMultiArityExpr.Op.AND.make(SmtMultiArityExpr.Op.AND.make(xMemberA, xyMember), forAllU);

        SmtExpr existsX = SmtQtExpr.Op.EXISTS.make(existsXBody, x);
        SmtExpr loneEast = SmtMultiArityExpr.Op.OR.make(SmtQtExpr.Op.FORALL.make(notXY, x), existsX);
        SmtExpr yImplies = SmtBinaryExpr.Op.IMPLIES.make(yMemberB, loneEast);
        SmtExpr forAllY = SmtQtExpr.Op.FORALL.make(yImplies, y);

        SmtExpr and = SmtMultiArityExpr.Op.AND.make(subset, forAllY);
        SmtQtExpr existsSet = SmtQtExpr.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);

        return multiplicitySet.getVariable();
    }

    private SmtExpr getTupleConcatenation(SetSort ASort, SetSort BSort, SmtVariable x, SmtVariable y)
    {
        List<SmtExpr> tupleElements = new ArrayList<>();
        for (int i = 0; i < ((TupleSort) ASort.elementSort).elementSorts.size(); i++)
        {
            IntConstant index = IntConstant.getInstance(i);
            tupleElements.add(SmtBinaryExpr.Op.TUPSEL.make(index, x.getVariable()));
        }

        for (int i = 0; i < ((TupleSort) BSort.elementSort).elementSorts.size(); i++)
        {
            IntConstant index = IntConstant.getInstance(i);
            tupleElements.add(SmtBinaryExpr.Op.TUPSEL.make(index, y.getVariable()));
        }

        return SmtMultiArityExpr.Op.MKTUPLE.make(tupleElements);
    }

    private SmtExpr translateImplies(ExprBinary expr, Environment environment)
    {
        Environment environmentA = new Environment(environment);
        Environment environmentB = new Environment(environment);
        SmtExpr A = exprTranslator.translateExpr(expr.left, environmentA);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environmentB);
        SmtExpr implies = SmtBinaryExpr.Op.IMPLIES.make(A, B);

        SmtExpr finalSmtExpr = exprTranslator.translateAuxiliaryFormula(implies, environmentA);
        finalSmtExpr = exprTranslator.translateAuxiliaryFormula(finalSmtExpr, environmentB);
        return finalSmtExpr;
    }

    private SmtExpr translateAnd(ExprBinary expr, Environment environment)
    {
        Environment environmentA = new Environment(environment);
        Environment environmentB = new Environment(environment);
        SmtExpr A = exprTranslator.translateExpr(expr.left, environmentA);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environmentB);
        SmtExpr and = SmtMultiArityExpr.Op.AND.make(A, B);

        SmtExpr finalSmtExpr = exprTranslator.translateAuxiliaryFormula(and, environmentA);
        finalSmtExpr = exprTranslator.translateAuxiliaryFormula(finalSmtExpr, environmentB);
        return finalSmtExpr;
    }

    private SmtExpr translateOr(ExprBinary expr, Environment environment)
    {
        Environment environmentA = new Environment(environment);
        Environment environmentB = new Environment(environment);
        SmtExpr A = exprTranslator.translateExpr(expr.left, environmentA);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environmentB);
        SmtExpr or = SmtMultiArityExpr.Op.OR.make(A, B);

        SmtExpr finalSmtExpr = exprTranslator.translateAuxiliaryFormula(or, environmentA);
        finalSmtExpr = exprTranslator.translateAuxiliaryFormula(finalSmtExpr, environmentB);
        return finalSmtExpr;
    }

    private SmtExpr translateArrow(ExprBinary expr, Environment environment)
    {
        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);
        SmtExpr product = SmtBinaryExpr.Op.PRODUCT.make(A, B);
        return product;
    }

    private SmtExpr translatePlusPlus(ExprBinary expr, Environment environment)
    {
        int rightExprArity = expr.right.type().arity();
        if (rightExprArity == 1)
        {
            // ++ is like a single + with arity 1 (i.e. is like a union)
            return translateSetOperation(expr, SmtBinaryExpr.Op.UNION, environment);
        }
        else
        {
            SmtExpr left = exprTranslator.translateExpr(expr.left, environment);
            SmtExpr right = exprTranslator.translateExpr(expr.right, environment);
            SmtExpr join = right;

            for (int i = 0; i < rightExprArity - 1; ++i)
            {
                join = SmtBinaryExpr.Op.JOIN.make(join, AbstractTranslator.univAtom.getVariable());
            }
            for (int i = 0; i < rightExprArity - 1; ++i)
            {
                join = SmtBinaryExpr.Op.PRODUCT.make(join, AbstractTranslator.univAtom.getVariable());
            }

            SmtExpr intersection = SmtBinaryExpr.Op.INTERSECTION.make(join, left);
            SmtExpr difference = SmtBinaryExpr.Op.SETMINUS.make(left, intersection);
            SmtExpr union = SmtBinaryExpr.Op.UNION.make(difference, right);

            return union;

        }
    }

    private SmtExpr translateDomainRestriction(ExprBinary expr, Environment environment)
    {
        int arity = expr.right.type().arity();

        if (arity <= 1)
        {
            // arity should be greater than one
            throw new UnsupportedOperationException();
        }
        else
        {
            SmtExpr left = exprTranslator.translateExpr(expr.left, environment);
            SmtExpr right = exprTranslator.translateExpr(expr.right, environment);

            // right type should be a set of tuples
            SetSort rightSort = (SetSort) right.getSort();
            TupleSort tuple = (TupleSort) rightSort.elementSort;
            for (int i = 1; i < arity; i++)
            {
                UninterpretedSort sort = (UninterpretedSort) tuple.elementSorts.get(i);
                if (sort.equals(AbstractTranslator.atomSort))
                {
                    left = SmtBinaryExpr.Op.PRODUCT.make(left, translator.univAtom.getVariable());
                }
                else
                {
                    left = SmtBinaryExpr.Op.PRODUCT.make(left, translator.univInt.getVariable());
                }
            }
            SmtBinaryExpr intersection = SmtBinaryExpr.Op.INTERSECTION.make(left, right);
            return intersection;
        }
    }

    private SmtExpr translateRangeRestriction(ExprBinary expr, Environment environment)
    {
        int arity = expr.left.type().arity();

        if (arity <= 1)
        {
            // arity should be greater than one
            throw new UnsupportedOperationException();
        }
        else
        {
            SmtExpr left = exprTranslator.translateExpr(expr.left, environment);
            SmtExpr right = exprTranslator.translateExpr(expr.right, environment);

            // left type should be a set of tuples
            SetSort leftSort = (SetSort) left.getSort();
            TupleSort tuple = (TupleSort) leftSort.elementSort;
            for (int i = 0; i < arity - 1; i++)
            {
                UninterpretedSort sort = (UninterpretedSort) tuple.elementSorts.get(i);
                if (sort.equals(AbstractTranslator.atomSort))
                {
                    right = SmtBinaryExpr.Op.PRODUCT.make(translator.univAtom.getVariable(), right);
                }
                else
                {
                    right = SmtBinaryExpr.Op.PRODUCT.make(translator.univInt.getVariable(), right);
                }
            }

            SmtBinaryExpr intersection = SmtBinaryExpr.Op.INTERSECTION.make(left, right);

            return intersection;
        }
    }

    private SmtExpr translateComparison(ExprBinary expr, SmtBinaryExpr.Op op, Environment environment)
    {
        // Right hand side is a expression and right hand side is a constant
        if (((expr.left instanceof ExprUnary) && ((ExprUnary) expr.left).op == ExprUnary.Op.CARDINALITY &&
                (expr.right instanceof ExprConstant)))
        {
            return translateCardinality(expr, op, environment);
        }
        else if ((expr.right instanceof ExprUnary) && ((ExprUnary) expr.right).op == ExprUnary.Op.CARDINALITY &&
                (expr.left instanceof ExprConstant))
        {
            return translateCardinality(expr, op, environment);
        }
        else
        {
            SmtExpr leftExpr = exprTranslator.translateExpr(expr.left, environment);
            SmtExpr rightExpr = exprTranslator.translateExpr(expr.right, environment);
            SmtExpr comparisonExpr = getComparison(op, leftExpr, rightExpr);
            return exprTranslator.translateAuxiliaryFormula(comparisonExpr, environment);
        }
    }

    private SmtExpr getComparison(SmtBinaryExpr.Op op, SmtExpr left, SmtExpr right)
    {
        SmtVariable x = new SmtVariable("x", AbstractTranslator.uninterpretedInt, false);
        SmtVariable y = new SmtVariable("y", AbstractTranslator.uninterpretedInt, false);
        SmtExpr xTuple = new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, x.getVariable());
        SmtExpr yTuple = new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, y.getVariable());
        SmtExpr xSingleton = SmtUnaryExpr.Op.SINGLETON.make(xTuple);
        SmtExpr ySingleton = SmtUnaryExpr.Op.SINGLETON.make(yTuple);
        SmtExpr xValue = new SmtCallExpr(AbstractTranslator.uninterpretedIntValue, x.getVariable());
        SmtExpr yValue = new SmtCallExpr(AbstractTranslator.uninterpretedIntValue, y.getVariable());

        SmtExpr relation1EqualsX = SmtBinaryExpr.Op.EQ.make(xSingleton, left);
        SmtExpr relation2EqualsY = SmtBinaryExpr.Op.EQ.make(ySingleton, right);
        SmtExpr and1 = SmtMultiArityExpr.Op.AND.make(relation1EqualsX, relation2EqualsY);

        SmtExpr comparison = op.make(xValue, yValue);
        SmtExpr and2 = SmtMultiArityExpr.Op.AND.make(and1, comparison);
        SmtExpr exists = SmtQtExpr.Op.EXISTS.make(and2, Arrays.asList(x, y));

        //ToDo: remove these 2 lines
//        Assertion assertion = new Assertion(left + " " + op + " " + right , exists);
//        exprTranslator.translator.smtProgram.addAssertion(assertion);
        return exists;
    }

    private SmtExpr translateEqComparison(ExprBinary expr, SmtBinaryExpr.Op op, Environment environment)
    {

        if ((expr.left instanceof ExprUnary &&
                ((ExprUnary) expr.left).op == ExprUnary.Op.CARDINALITY) ||
                (expr.right instanceof ExprUnary &&
                        ((ExprUnary) expr.right).op == ExprUnary.Op.CARDINALITY)
        )
        {
            return translateCardinality(expr, op, environment);
        }

        Environment environmentA = new Environment(environment);
        Environment environmentB = new Environment(environment);
        SmtExpr A = exprTranslator.translateExpr(expr.left, environmentA);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environmentB);

        A = TranslatorUtils.makeRelation(A);
        B = TranslatorUtils.makeRelation(B);

        if (A.getSort().equals(AbstractTranslator.setOfIntSortTuple))
        {
            A = exprTranslator.translator.handleIntConstant(A);
        }

        if (B.getSort().equals(AbstractTranslator.setOfIntSortTuple))
        {
            B = exprTranslator.translator.handleIntConstant(B);
        }

        SmtExpr equality = SmtBinaryExpr.Op.EQ.make(A, B);

        SmtExpr finalSmtExpr = exprTranslator.translateAuxiliaryFormula(equality, environmentA);
        finalSmtExpr = exprTranslator.translateAuxiliaryFormula(finalSmtExpr, environmentB);
        return finalSmtExpr;
    }

    private SmtExpr translateCardinality(ExprBinary expr, SmtBinaryExpr.Op op, Environment environment)
    {
        // CVC4 doesn't support comparison  between 2 cardinality expressions
        if
        (expr.left instanceof ExprUnary &&
                ((ExprUnary) expr.left).op == ExprUnary.Op.CARDINALITY &&
                expr.right instanceof ExprUnary &&
                ((ExprUnary) expr.right).op == ExprUnary.Op.CARDINALITY
        )
        {
            throw new UnsupportedOperationException("CVC4 doesn't support comparision between 2 cardinality expressions.");
        }

        if
        (
                (expr.left instanceof ExprUnary &&
                        ((ExprUnary) expr.left).op == ExprUnary.Op.CARDINALITY &&
                        (!(expr.right instanceof ExprConstant &&
                                ((ExprConstant) expr.right).op == ExprConstant.Op.NUMBER))) ||
                        (expr.right instanceof ExprUnary &&
                                ((ExprUnary) expr.right).op == ExprUnary.Op.CARDINALITY &&
                                (!(expr.left instanceof ExprConstant &&
                                        ((ExprConstant) expr.left).op == ExprConstant.Op.NUMBER)))
        )
        {
            throw new UnsupportedOperationException("CVC4 only supports cardinality with constant numbers");
        }


        // translate cardinality differently
        if
        ((expr.left instanceof ExprUnary &&
                ((ExprUnary) expr.left).op == ExprUnary.Op.CARDINALITY)
        )
        {
            int n = ((ExprConstant) expr.right).num;
            SmtExpr equality = translateCardinalityComparison((ExprUnary) expr.left, n, op, environment);
            return equality;
        }

        if
        ((expr.right instanceof ExprUnary &&
                ((ExprUnary) expr.right).op == ExprUnary.Op.CARDINALITY)
        )
        {
            int n = ((ExprConstant) expr.left).num;
            SmtExpr equality = translateCardinalityComparison((ExprUnary) expr.right, n, op, environment);
            return equality;
        }

        throw new UnsupportedOperationException();
    }

    private SmtExpr translateCardinalityComparison(ExprUnary expr, int n, SmtBinaryExpr.Op op, Environment environment)
    {
        Environment newEnvironment = new Environment(environment);
        SmtExpr setExpr = exprTranslator.translateExpr(expr.sub, newEnvironment);
        SetSort setSort = (SetSort) setExpr.getSort();
        Sort elementSort = setSort.elementSort;

        // shared code
        SmtExpr emptySet = SmtUnaryExpr.Op.EMPTYSET.make(setSort);
        SmtExpr isEmpty = SmtBinaryExpr.Op.EQ.make(setExpr, emptySet);
        SmtExpr notEmpty = SmtUnaryExpr.Op.NOT.make(isEmpty);

        switch (op)
        {
            case EQ:
            {
                if (n < 0)
                {
                    // impossible
                    return exprTranslator.translateAuxiliaryFormula(BoolConstant.False, newEnvironment);
                }

                if (n == 0)
                {
                    // empty set
                    return exprTranslator.translateAuxiliaryFormula(isEmpty, newEnvironment);
                }

                List<SmtVariable> vars = generateVariables(n, elementSort);
                SmtExpr cardinalitySet = generateCardinalitySet(vars);
                SmtExpr equalExpr = SmtBinaryExpr.Op.EQ.make(setExpr, cardinalitySet);
                SmtExpr andExpr = makeDistinct(equalExpr, vars);
                SmtExpr exists = SmtQtExpr.Op.EXISTS.make(andExpr, vars);
                return exprTranslator.translateAuxiliaryFormula(exists, newEnvironment);
            }

            case LT:
            {
                if (n <= 0)
                {
                    // impossible
                    return exprTranslator.translateAuxiliaryFormula(BoolConstant.False, newEnvironment);
                }

                if (n == 1)
                {
                    // empty set
                    return exprTranslator.translateAuxiliaryFormula(isEmpty, newEnvironment);
                }

                List<SmtVariable> vars = generateVariables(n - 1, elementSort);
                SmtExpr cardinalitySet = generateCardinalitySet(vars);
                SmtExpr subsetExpr = SmtBinaryExpr.Op.SUBSET.make(setExpr, cardinalitySet);
                SmtExpr andExpr = makeDistinct(subsetExpr, vars);
                SmtExpr exists = SmtQtExpr.Op.EXISTS.make(andExpr, vars);
                return exprTranslator.translateAuxiliaryFormula(exists, newEnvironment);
            }

            case LTE:
            {
                if (n <= -1)
                {
                    // impossible
                    return exprTranslator.translateAuxiliaryFormula(BoolConstant.False, newEnvironment);
                }

                if (n == 0)
                {
                    // empty set
                    return exprTranslator.translateAuxiliaryFormula(isEmpty, newEnvironment);
                }

                List<SmtVariable> vars = generateVariables(n, elementSort);
                SmtExpr cardinalitySet = generateCardinalitySet(vars);
                SmtExpr subsetExpr = SmtBinaryExpr.Op.SUBSET.make(setExpr, cardinalitySet);
                SmtExpr andExpr = makeDistinct(subsetExpr, vars);
                SmtExpr exists = SmtQtExpr.Op.EXISTS.make(andExpr, vars);
                return exprTranslator.translateAuxiliaryFormula(exists, newEnvironment);
            }

            case GT:
            {
                if (n <= -1)
                {
                    // valid
                    return exprTranslator.translateAuxiliaryFormula(BoolConstant.True, newEnvironment);
                }
                if(n == 0)
                {
                    // not empty
                    return exprTranslator.translateAuxiliaryFormula(notEmpty, newEnvironment);
                }

                List<SmtVariable> vars = generateVariables(n + 1, elementSort);
                SmtExpr cardinalitySet = generateCardinalitySet(vars);
                SmtExpr subsetExpr = SmtBinaryExpr.Op.SUBSET.make(cardinalitySet, setExpr);
                SmtExpr andExpr = makeDistinct(subsetExpr, vars);
                SmtExpr exists = SmtQtExpr.Op.EXISTS.make(andExpr, vars);
                return exprTranslator.translateAuxiliaryFormula(exists, newEnvironment);
            }

            case GTE:
            {
                if (n <= 0)
                {
                    // valid
                    return exprTranslator.translateAuxiliaryFormula(BoolConstant.True, newEnvironment);
                }

                if(n == 1)
                {
                    // not empty
                    return exprTranslator.translateAuxiliaryFormula(notEmpty, newEnvironment);
                }

                List<SmtVariable> vars = generateVariables(n, elementSort);
                SmtExpr cardinalitySet = generateCardinalitySet(vars);
                SmtExpr subsetExpr = SmtBinaryExpr.Op.SUBSET.make(cardinalitySet, setExpr);
                SmtExpr andExpr = makeDistinct(subsetExpr, vars);
                SmtExpr exists = SmtQtExpr.Op.EXISTS.make(andExpr, vars);
                return exprTranslator.translateAuxiliaryFormula(exists, newEnvironment);
            }

            default:
            {
                throw new RuntimeException("Unexpected cardinality operator" + op);
            }
        }
    }

    private SmtExpr makeDistinct(SmtExpr boolExpr, List<SmtVariable> vars)
    {
        assert (boolExpr.getSort().equals(AbstractTranslator.boolSort));
        if (vars.size() == 1)
        {
            return boolExpr;
        }
        List<SmtExpr> exprs = vars.stream().map(v -> v.getVariable()).collect(Collectors.toList());
        SmtExpr distinct = SmtMultiArityExpr.Op.DISTINCT.make(exprs);
        SmtExpr and = SmtMultiArityExpr.Op.AND.make(boolExpr, distinct);
        return and;
    }

    private SmtExpr generateCardinalitySet(List<SmtVariable> vars)
    {
        assert (vars.size() >= 1);

        SmtExpr set = SmtUnaryExpr.Op.SINGLETON.make(vars.get(0).getVariable());

        if (vars.size() == 1)
        {
            return set;
        }

        for (int i = 1; i < vars.size(); i++)
        {
            set = SmtMultiArityExpr.Op.INSERT.make(vars.get(i).getVariable(), set);
        }

        return set;
    }

    private List<SmtVariable> generateVariables(int n, Sort elementSort)
    {
        if (n <= 0)
        {
            throw new RuntimeException(String.format("Expected %1$d  to be greater than zero. ", n));
        }
        List<SmtVariable> vars = new ArrayList<>();
        for (int i = 0; i < n; i++)
        {
            String freshName = TranslatorUtils.getFreshName(elementSort);
            vars.add(new SmtVariable(freshName, elementSort, false));
        }
        return vars;
    }

    private SmtExpr translateSetOperation(ExprBinary expr, SmtBinaryExpr.Op op, Environment environment)
    {
        SmtExpr left = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr right = exprTranslator.translateExpr(expr.right, environment);

        if (left instanceof Variable &&
                (!(((Variable) left).getDeclaration().getSort() instanceof SetSort)))
        {
            left = TranslatorUtils.makeRelation((Variable) left);
        }
        else if (left instanceof SmtMultiArityExpr &&
                ((SmtMultiArityExpr) left).getOp() == SmtMultiArityExpr.Op.MKTUPLE)
        {
            left = AlloyUtils.mkSingletonOutOfTuple((SmtMultiArityExpr) left);
        }
        if (right instanceof Variable &&
                (!(((Variable) right).getDeclaration().getSort() instanceof SetSort)))
        {
            right = TranslatorUtils.makeRelation((Variable) right);
        }
        else if (right instanceof SmtMultiArityExpr &&
                ((SmtMultiArityExpr) right).getOp() == SmtMultiArityExpr.Op.MKTUPLE)
        {
            right = AlloyUtils.mkSingletonOutOfTuple((SmtMultiArityExpr) right);
        }

        SmtBinaryExpr operation = op.make(left, right);
        return operation;
    }

    private SmtExpr translateSubsetOperation(ExprBinary expr, Environment environment)
    {
        Environment environmentA = new Environment(environment);
        SmtExpr A = exprTranslator.translateExpr(expr.left, environmentA);
        A = exprTranslator.translator.handleIntConstant(A);

        Environment environmentB = new Environment(environmentA);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environmentB);
        B = exprTranslator.translator.handleIntConstant(B);

        // left sort | right sort | Translation
        // -------------------------------------
        // tuple     | tuple      | (= A B)
        // tuple     | set        | (member tuple set)
        // set       | set        | (subset A B)
        SmtExpr translation;
        if (A.getSort() instanceof TupleSort && B.getSort() instanceof TupleSort)
        {
            translation = SmtBinaryExpr.Op.EQ.make(A, B);
        }
        else if (A.getSort() instanceof SetSort && B.getSort() instanceof SetSort)
        {
            translation = SmtBinaryExpr.Op.SUBSET.make(A, B);
        }
        else if (A.getSort() instanceof TupleSort && B.getSort() instanceof SetSort)
        {
            translation = SmtBinaryExpr.Op.MEMBER.make(A, B);
        }
        else
        {
            A = SmtMultiArityExpr.Op.MKTUPLE.make(A);
            translation = SmtBinaryExpr.Op.MEMBER.make(A, B);
        }

        translation = exprTranslator.translateAuxiliaryFormula(translation, environmentB);

        return translation;
    }

    private SmtExpr translateJoin(ExprBinary expr, Environment environment)
    {
        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);
        A = TranslatorUtils.makeRelation(A);
        B = TranslatorUtils.makeRelation(B);
        SmtBinaryExpr join = SmtBinaryExpr.Op.JOIN.make(A, B);
        return join;
    }

    public SmtExpr translateArithmetic(ExprBinary expr, SmtBinaryExpr.Op op, Environment environment)
    {
        SmtExpr A = exprTranslator.translateExpr(expr.left, environment);
        SmtExpr B = exprTranslator.translateExpr(expr.right, environment);
        A = convertIntConstantToSet(A);

        B = convertIntConstantToSet(B);

        if (A.getSort().equals(AbstractTranslator.setOfIntSortTuple))
        {
            A = translator.handleIntConstant(A);
        }

        if (B.getSort().equals(AbstractTranslator.setOfIntSortTuple))
        {
            B = translator.handleIntConstant(B);
        }

        String freshName = TranslatorUtils.getFreshName(AbstractTranslator.setOfUninterpretedIntTuple);

        SmtVariable x = new SmtVariable("x", AbstractTranslator.uninterpretedInt, false);
        SmtVariable y = new SmtVariable("y", AbstractTranslator.uninterpretedInt, false);
        SmtVariable z = new SmtVariable("z", AbstractTranslator.uninterpretedInt, false);

        SmtExpr xTuple = new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, x.getVariable());
        SmtExpr yTuple = new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, y.getVariable());
        SmtExpr zTuple = new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, z.getVariable());

        SmtExpr xValue = new SmtCallExpr(AbstractTranslator.uninterpretedIntValue, x.getVariable());
        SmtExpr yValue = new SmtCallExpr(AbstractTranslator.uninterpretedIntValue, y.getVariable());
        SmtExpr zValue = new SmtCallExpr(AbstractTranslator.uninterpretedIntValue, z.getVariable());

        SmtExpr xyOperation = op.make(xValue, yValue);
        SmtExpr equal = SmtBinaryExpr.Op.EQ.make(xyOperation, zValue);

        if (translator.alloySettings.integerSingletonsOnly)
        {
            // A= {x}, B = {y} => Result = {z} where z = (x operation y)
            SmtExpr xSingleton = SmtUnaryExpr.Op.SINGLETON.make(xTuple);
            SmtExpr ySingleton = SmtUnaryExpr.Op.SINGLETON.make(yTuple);
            SmtExpr singletonA = SmtBinaryExpr.Op.EQ.make(A, xSingleton);
            SmtExpr singletonB = SmtBinaryExpr.Op.EQ.make(B, ySingleton);

            SmtExpr and = SmtMultiArityExpr.Op.AND.make(equal, singletonA, singletonB);

            SmtQtExpr exists = SmtQtExpr.Op.EXISTS.make(and, x, y, z);
            environment.addAuxiliaryFormula(exists);
            return z.getVariable();
        }

        SmtVariable result = new SmtVariable(freshName, AbstractTranslator.setOfUninterpretedIntTuple, false);
        SmtExpr resultSmtExpr = result.getVariable();

        // for all z : uninterpretedInt. x in Result implies
        // exists x, y :uninterpretedInt. x in A and y in B and (x, y, z) in operation

        SmtExpr xMember = SmtBinaryExpr.Op.MEMBER.make(xTuple, A);
        SmtExpr yMember = SmtBinaryExpr.Op.MEMBER.make(yTuple, B);
        SmtExpr zMember = SmtBinaryExpr.Op.MEMBER.make(zTuple, resultSmtExpr);

        SmtExpr xyMember = SmtMultiArityExpr.Op.AND.make(xMember, yMember);
        SmtExpr and2 = SmtMultiArityExpr.Op.AND.make(equal, xyMember);
        SmtExpr exists1 = SmtQtExpr.Op.EXISTS.make(and2, x, y);

        SmtExpr implies1 = SmtBinaryExpr.Op.IMPLIES.make(zMember, exists1);
        SmtExpr axiom1 = SmtQtExpr.Op.FORALL.make(implies1, z);


        // for all x, y : uninterpretedInt. x in A and y in B implies
        // exists z :uninterpretedInt. x in Result and (x, y, z) in operation

        SmtExpr and3 = SmtMultiArityExpr.Op.AND.make(equal, zMember);
        SmtExpr exists2 = SmtQtExpr.Op.EXISTS.make(and3, z);

        SmtExpr implies2 = SmtBinaryExpr.Op.IMPLIES.make(xyMember, exists2);
        SmtExpr axiom2 = SmtQtExpr.Op.FORALL.make(implies2, x, y);

        SmtExpr axioms = SmtMultiArityExpr.Op.AND.make(axiom1, axiom2);
        SmtQtExpr exists = SmtQtExpr.Op.EXISTS.make(axioms, result);
        environment.addAuxiliaryFormula(exists);

        return resultSmtExpr;
    }

    private SmtExpr convertIntConstantToSet(SmtExpr A)
    {
        if (A instanceof IntConstant)
        {
            FunctionDeclaration uninterpretedInt = translator.getUninterpretedIntConstant((IntConstant) A);
            SmtExpr tuple = new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, uninterpretedInt.getVariable());
            if (translator.alloySettings.integerSingletonsOnly)
            {
                A = SmtUnaryExpr.Op.SINGLETON.make(tuple);
            }
            else
            {
                A = tuple;
            }
        }
        return A;
    }
}
