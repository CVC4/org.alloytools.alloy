/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt;

import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class TranslatorUtils
{
    private static int nameIndex = 0;

    private static int atomIndex = 0;

    private static int setIndex = 0;

    /**
     * Sanitize string s by replacing "\" with "_".
     */
    public static String sanitizeName(String s)
    {
        return s.replaceAll("/", "_").replaceAll("'", "_").replaceAll("\"", "_");
    }

    public static FunctionDeclaration generateAuxiliarySetNAtoms(int arity, int n, AbstractTranslator translator)
    {
        List<Sort> sorts = IntStream.range(1, arity + 1).boxed().map(x -> translator.atomSort).collect(Collectors.toList());
        Sort tupleSort = new TupleSort(sorts);
        Sort setSort = new SetSort(tupleSort);

        //ToDo: handle the case when n = 0
        List<Expression> expressions = declareNDistinctConstants(tupleSort, n, translator.smtProgram);

        FunctionDeclaration declaration = new FunctionDeclaration(getNewSetName(), setSort);

        translator.smtProgram.addFunction(declaration);

        Expression set = new UnaryExpression(UnaryExpression.Op.SINGLETON, expressions.get(expressions.size() - 1));

        if (expressions.size() > 1)
        {
            List<Expression> atoms = new ArrayList<>();

            for (int i = 0; i < expressions.size() - 1; i++)
            {
                atoms.add(expressions.get(i));
            }

            atoms.add(set);

            set = new MultiArityExpression(MultiArityExpression.Op.INSERT, atoms);
        }

        BinaryExpression equality = new BinaryExpression(declaration.getVariable(), BinaryExpression.Op.EQ, set);

        translator.smtProgram.addAssertion(new Assertion(equality));

        return declaration;
    }

    public static List<Expression> declareNDistinctConstants(Sort sort, int n, SmtProgram smtProgram)
    {
        List<Expression> expressions = new ArrayList<>();
        if (n > 0)
        {
            for (int i = 0; i < n; i++)
            {
                ConstantDeclaration constantDeclaration = new ConstantDeclaration(getNewAtomName(), sort);
                expressions.add(constantDeclaration.getVariable());
                smtProgram.addConstantDeclaration(constantDeclaration);
            }

            if (n > 1)
            {
                MultiArityExpression distinct = new MultiArityExpression(MultiArityExpression.Op.DISTINCT, expressions);
                smtProgram.addAssertion(new Assertion(distinct));
            }
        }
        else
        {
            throw new UnsupportedOperationException("Argument n should be greater than 0");
        }
        return expressions;
    }

    public static String getNewName()
    {
        nameIndex++;
        return "_x" + nameIndex;
    }

    public static String getNewAtomName()
    {
        atomIndex++;
        return "_a" + atomIndex;
    }

    public static String getNewSetName()
    {
        setIndex++;
        return "_S" + setIndex;
    }

    public static void reset()
    {
        nameIndex = 0;
        atomIndex = 0;
        setIndex = 0;
    }

    public static Sort getSetSortOfAtomWithArity(int n)
    {
        List<Sort> elementSorts = new ArrayList<>();
        for (int i = 0; i < n; ++i)
        {
            elementSorts.add(AbstractTranslator.atomSort);
        }
        return new SetSort(new TupleSort(elementSorts));
    }

    public static Expression mkDistinctExpr(Expression... exprs)
    {
        if (exprs == null)
        {
            throw new RuntimeException();
        }
        else if (exprs.length == 1)
        {
            return exprs[0];
        }
        else
        {
            return new MultiArityExpression(MultiArityExpression.Op.DISTINCT, exprs);
        }
    }

    public static Expression mkDistinctExpr(List<Expression> exprs)
    {
        if (exprs == null)
        {
            throw new RuntimeException();
        }
        else if (exprs.isEmpty() || exprs.size() == 1)
        {
            return new BoolConstant(true);
        }
        else
        {
            return new MultiArityExpression(MultiArityExpression.Op.DISTINCT, exprs);
        }
    }

    public static Expression getTuple(Declaration... elements)
    {
        List<Expression> expressions = Arrays.stream(elements)
                                             .map(Declaration::getVariable).collect(Collectors.toList());
        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, expressions);
    }

    public static Expression getTuple(Expression... expressions)
    {
        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, expressions);
    }
}