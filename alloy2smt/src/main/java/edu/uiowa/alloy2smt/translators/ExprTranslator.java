/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.uiowa.alloy2smt.smtAst.*;

import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;

public class ExprTranslator
{
    final Alloy2SmtTranslator translator;

    final ExprUnaryTranslator exprUnaryTranslator;

    final ExprBinaryTranslator exprBinaryTranslator;

    public ExprTranslator(Alloy2SmtTranslator translator)
    {
        this.translator             = translator;
        this.exprUnaryTranslator    = new ExprUnaryTranslator(this);
        this.exprBinaryTranslator   = new ExprBinaryTranslator(this);
    }

    Expression translateExpr(Expr expr)
    {
        return translateExpr(expr, new HashMap<>());
    }

    Expression translateExpr(Expr expr, Map<String, Expression> variablesScope)
    {
        if(expr instanceof ExprUnary)
        {
            return this.exprUnaryTranslator.translateExprUnary((ExprUnary) expr, variablesScope);
        } 
        else if(expr instanceof ExprBinary)
        {
            return this.exprBinaryTranslator.translateExprBinary((ExprBinary) expr, variablesScope);
        }
        else if(expr instanceof ExprQt)
        {
            return translateExprQt((ExprQt) expr, variablesScope);
        }
        else if(expr instanceof ExprConstant)
        {
            return translateExprConstant((ExprConstant) expr, variablesScope);
        }
        else if(expr instanceof ExprList)
        {
            return translateExprList((ExprList) expr, variablesScope);
        }
        else if(expr instanceof ExprCall)
        {
            return translateExprCall((ExprCall) expr, variablesScope);
        }
        else if(expr instanceof ExprITE)
        {
            return translateExprITE((ExprITE) expr, variablesScope);
        }
        else if(expr instanceof ExprLet)
        {
            return translateExprLet((ExprLet) expr, variablesScope);
        }  

        throw new UnsupportedOperationException(((ExprCall) expr).toString());
    }
    
    public Expression translateExprITE(ExprITE expr, Map<String,Expression> variablesScope)
    {
        Expression condExpr = translateExpr(expr.cond, variablesScope);
        Expression thenExpr = translateExpr(expr.left, variablesScope);
        Expression elseExpr = translateExpr(expr.right, variablesScope);
        return new ITEExpression(condExpr, thenExpr, elseExpr);
    }

    public Expression translateExprConstant(ExprConstant expr, Map<String,Expression> variablesScope)
    {
        switch (expr.op)
        {
            // alloy only supports integers
            case NUMBER : return new IntConstant(expr.num); 
            case IDEN   : return translator.atomIden.getConstantExpr();
            case TRUE   : return new BooleanConstant(true);
            case FALSE  : return new BooleanConstant(false); 
            default: throw new UnsupportedOperationException(expr.op.name());
        }
    }   

    Expression translateExprList(ExprList exprList, Map<String, Expression> variablesScope)
    {
        switch (exprList.op)
        {
            case AND        : return translateExprListToBinaryExpressions(BinaryExpression.Op.AND, exprList, variablesScope);
            case OR         : return translateExprListToBinaryExpressions(BinaryExpression.Op.OR, exprList, variablesScope);
            case DISJOINT   : return translateExprListToDisjBinaryExpressions(MultiArityExpression.Op.DISTINCT, exprList, variablesScope);
            case TOTALORDER : throw new UnsupportedOperationException();// total order should be handled before coming here
            default         : throw new UnsupportedOperationException();
        }
    }

    Expression translateExprListToDisjBinaryExpressions(MultiArityExpression.Op op, ExprList exprList, Map<String, Expression> variablesScope)
    {        
        List<Expression> exprs = new ArrayList<>();
        
        for(Expr e : exprList.args)
        {
            exprs.add(translateExpr(e, variablesScope));
        }
        Expression finalExpr;
        List<Expression> finalExprs = new ArrayList<>();
        
        if(exprs.size() > 1)
        {
            for(int i = 0; i < exprs.size()-1; ++i)
            {
                Expression disjExpr = new BinaryExpression(translator.atomNone.getConstantExpr(), BinaryExpression.Op.EQ, new BinaryExpression(exprs.get(i), BinaryExpression.Op.INTERSECTION, exprs.get(i+1)));
                finalExprs.add(disjExpr);
            }
            finalExpr = finalExprs.get(0);
            for(int i = 1; i < finalExprs.size(); ++i)
            {
                finalExpr = new BinaryExpression(finalExpr, BinaryExpression.Op.AND, finalExprs.get(i));
            }
        }
        else
        {
            finalExpr = exprs.get(0);
        }
        return finalExpr;
    }
    
    Expression translateExprLet(ExprLet exprLet, Map<String, Expression> variablesScope)
    {
        Expression              varExpr         = translateExpr(exprLet.expr, variablesScope);
        Map<String, Expression> varToExprMap    = new HashMap<>();
        String                  sanitizeName    = TranslatorUtils.sanitizeName(exprLet.var.label);
        List<Sort>              exprSorts       = getExprSorts(exprLet.expr);
        ConstantExpression      varDeclExpr     = new ConstantExpression(new ConstantDeclaration(sanitizeName, new SetSort(new TupleSort(exprSorts))));
        
        varToExprMap.put(sanitizeName, varExpr);        
        variablesScope.put(exprLet.var.label, varDeclExpr);
        
        Expression letBodyExpr = translateExpr(exprLet.sub, variablesScope);
        return new LetExpression(LetExpression.Op.LET, varToExprMap, letBodyExpr);
    }    
    
    Expression translateExprCall(ExprCall exprCall, Map<String, Expression> variablesScope)
    {
        String              funcName = exprCall.fun.label;
        List<Expression>    argExprs = new ArrayList<>();
        
        for(Expr e : exprCall.args)
        {
            argExprs.add(translateExpr(e, variablesScope));
        }
        
        if(this.translator.funcNamesMap.containsKey(funcName))
        {
            return new FunctionCallExpression(translator.getFunctionFromAlloyName(funcName), argExprs);
        }
        else if(this.translator.setComprehensionFuncNameToInputsMap.containsKey(funcName))
        {
            return translateSetComprehensionFuncCallExpr(funcName, argExprs);
        }
        else if(funcName.equals("integer/plus") || funcName.equals("integer/add"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.PLUS, variablesScope);
        }
        else if(funcName.equals("integer/minus")|| funcName.equals("integer/sub"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.MINUS, variablesScope);
        }
        else if(funcName.equals("integer/mul"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.MULTIPLY, variablesScope);
        } 
        else if(funcName.equals("integer/div"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.DIVIDE, variablesScope);
        }
        else if(funcName.equals("integer/rem"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.MOD, variablesScope);
        }
        else if(translator.functionsMap.containsKey(TranslatorUtils.sanitizeName(funcName)))
        {
            FunctionDeclaration function = translator.getFunction(TranslatorUtils.sanitizeName(funcName));
            return new FunctionCallExpression(function, argExprs);
        }
        else
        {
            FunctionDeclaration function = translator.translateFunction(translator.nameToFuncMap.get(funcName));
            return new FunctionCallExpression(function, argExprs);
        }
    }
    
    public Expression translateSetComprehensionFuncCallExpr(String funcName, List<Expression> argExprs)
    {
        Map<String, Expression> letVars = new HashMap<>();
        List<String> inputs = translator.setComprehensionFuncNameToInputsMap.get(funcName);
        Expression setCompDef = translator.setCompFuncNameToDefMap.get(funcName);
        VariableDeclaration setBdVar = translator.setCompFuncNameToBdVarExprMap.get(funcName);
        
        for(int i = 0; i < argExprs.size(); ++i)
        {
            letVars.put(inputs.get(i), argExprs.get(i));
        }
        
        if(!letVars.isEmpty())
        {
            setCompDef = new LetExpression(LetExpression.Op.LET, letVars, setCompDef);
        }
        if(translator.auxExpr != null)
        {
            translator.auxExpr = new BinaryExpression(translator.auxExpr, BinaryExpression.Op.AND, setCompDef);
        }
        else
        {
            translator.auxExpr = setCompDef;
        }
        translator.existentialBdVars.add(setBdVar);
        return setBdVar.getConstantExpr();
    }
    
    public Expression translateArithmetic(Expression leftExpr, Expression rightExpr, BinaryExpression.Op op, Map<String,Expression> variablesScope)
    {
        if(!translator.arithOps.containsKey(op))
        {                      
            declArithmeticOp(op);
        }
        Expression operation = translator.arithOps.get(op);
        // (leftExpr, rightExpr, _) in operation
        //i.e. rightExpr o (leftExpr o operation) is not empty
        Expression leftExprJoin = new BinaryExpression(leftExpr, BinaryExpression.Op.JOIN, operation);
        Expression rightExprJoin = new BinaryExpression(rightExpr, BinaryExpression.Op.JOIN, leftExprJoin);
        Expression equal = new BinaryExpression(rightExprJoin, BinaryExpression.Op.EQ,
                new UnaryExpression(UnaryExpression.Op.EMPTYSET, Alloy2SmtTranslator.setOfUnaryIntSort));
        Expression not = new UnaryExpression(UnaryExpression.Op.NOT, equal);

        translator.smtProgram.addAssertion(new Assertion("Operands are in the relation", not));



        return new BinaryExpression(rightExpr, BinaryExpression.Op.JOIN, new BinaryExpression(leftExpr, BinaryExpression.Op.JOIN, operation));
    }

    public void declArithmeticOp(BinaryExpression.Op op)
    {
        VariableDeclaration bdUnaryIntVar1 = new VariableDeclaration("_x", translator.unaryIntTup);
        VariableDeclaration bdUnaryIntVar2 = new VariableDeclaration("_y", translator.unaryIntTup);
        VariableDeclaration bdUnaryIntVar3 = new VariableDeclaration("_z", translator.unaryIntTup);
        Expression bdIntVar1Expr = exprBinaryTranslator.mkTupleSelectExpr(exprUnaryTranslator.mkUnaryIntTupValue(bdUnaryIntVar1.getConstantExpr()), 0);
        Expression bdIntVar2Expr = exprBinaryTranslator.mkTupleSelectExpr(exprUnaryTranslator.mkUnaryIntTupValue(bdUnaryIntVar2.getConstantExpr()), 0);
        Expression bdIntVar3Expr = exprBinaryTranslator.mkTupleSelectExpr(exprUnaryTranslator.mkUnaryIntTupValue(bdUnaryIntVar3.getConstantExpr()), 0);                

        Expression memberOfOp = exprUnaryTranslator.mkOneTupleExprOutofAtoms(bdIntVar1Expr, bdIntVar2Expr, bdIntVar3Expr);

        VariableDeclaration existentialBdVar = new VariableDeclaration("_w", translator.ternaryIntTup);
        Expression rhsExpr  = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new BinaryExpression(new FunctionCallExpression(translator.valueOfTernaryIntTup, existentialBdVar.getConstantExpr()),
                                                    BinaryExpression.Op.EQ, memberOfOp), existentialBdVar);
//        Expression rhsExpr = new BooleanConstant(true);
        
        VariableDeclaration bdTernaryIntVar = new VariableDeclaration("_w", translator.ternaryIntTup);
        
        Expression ternaryIntTupExpr = new FunctionCallExpression(translator.valueOfTernaryIntTup, bdTernaryIntVar.getConstantExpr());

        Expression lhsExpr               = null;  
        Expression lhsExprII             = null; 
        Expression rhsExprII             = null; 
        Expression finalExprI            = null;
        Expression finalExprII           = null;
        ConstantDeclaration arithVarDecl = null;

        switch(op)
        {
            case PLUS:     
                arithVarDecl = new ConstantDeclaration("PLUS", translator.setOfTernaryIntSort);
                lhsExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.PLUS, bdIntVar2Expr);
                lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);
                rhsExpr = new BinaryExpression(rhsExpr, BinaryExpression.Op.AND, new BinaryExpression(memberOfOp, BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr()));
                finalExprI = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.IMPLIES, rhsExpr), bdUnaryIntVar1, bdUnaryIntVar2, bdUnaryIntVar3);
                
                lhsExprII = new BinaryExpression(ternaryIntTupExpr, BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr());
                rhsExprII = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.PLUS, bdIntVar2Expr);
                rhsExprII = new BinaryExpression(rhsExprII, BinaryExpression.Op.EQ, bdIntVar3Expr);
                rhsExprII = new BinaryExpression(rhsExprII, BinaryExpression.Op.AND, new BinaryExpression(ternaryIntTupExpr, BinaryExpression.Op.EQ, memberOfOp));
                rhsExprII = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, rhsExprII, bdUnaryIntVar1, bdUnaryIntVar2, bdUnaryIntVar3);
                finalExprII = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExprII, BinaryExpression.Op.IMPLIES, rhsExprII), bdTernaryIntVar);
                break;
            case MINUS:
                arithVarDecl = new ConstantDeclaration("MINUS", translator.setOfTernaryIntSort);
                lhsExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.MINUS, bdIntVar2Expr);
                lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);
                rhsExpr = new BinaryExpression(rhsExpr, BinaryExpression.Op.AND, new BinaryExpression(memberOfOp, BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr()));
                finalExprI = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.IMPLIES, rhsExpr), bdUnaryIntVar1, bdUnaryIntVar2, bdUnaryIntVar3);

                lhsExprII = new BinaryExpression(ternaryIntTupExpr, BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr());
                rhsExprII = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.MINUS, bdIntVar2Expr);
                rhsExprII = new BinaryExpression(rhsExprII, BinaryExpression.Op.EQ, bdIntVar3Expr);
                rhsExprII = new BinaryExpression(rhsExprII, BinaryExpression.Op.AND, new BinaryExpression(ternaryIntTupExpr, BinaryExpression.Op.EQ, memberOfOp));
                rhsExprII = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, rhsExprII, bdUnaryIntVar1, bdUnaryIntVar2, bdUnaryIntVar3);
                finalExprII = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExprII, BinaryExpression.Op.IMPLIES, rhsExprII), bdTernaryIntVar);
                break;
            case MULTIPLY:
                arithVarDecl = new ConstantDeclaration("MUL", translator.setOfTernaryIntSort);
                lhsExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.MULTIPLY, bdIntVar2Expr);
                lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);
                rhsExpr = new BinaryExpression(rhsExpr, BinaryExpression.Op.AND, new BinaryExpression(memberOfOp, BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr()));
                finalExprI = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.IMPLIES, rhsExpr), bdUnaryIntVar1, bdUnaryIntVar2, bdUnaryIntVar3);

                lhsExprII = new BinaryExpression(ternaryIntTupExpr, BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr());
                rhsExprII = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.MULTIPLY, bdIntVar2Expr);
                rhsExprII = new BinaryExpression(rhsExprII, BinaryExpression.Op.EQ, bdIntVar3Expr);
                rhsExprII = new BinaryExpression(rhsExprII, BinaryExpression.Op.AND, new BinaryExpression(ternaryIntTupExpr, BinaryExpression.Op.EQ, memberOfOp));
                rhsExprII = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, rhsExprII, bdUnaryIntVar1, bdUnaryIntVar2, bdUnaryIntVar3);
                finalExprII = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExprII, BinaryExpression.Op.EQ, rhsExprII), bdTernaryIntVar);                
                break;
            case DIVIDE:
                arithVarDecl = new ConstantDeclaration("DIV", translator.setOfTernaryIntSort);
                lhsExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.DIVIDE, bdIntVar2Expr);                    
                lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);
                lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.AND, new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(exprUnaryTranslator.mkSingletonOutOfAtomExpr(bdIntVar2Expr), BinaryExpression.Op.EQ, new IntConstant(0))));
                rhsExpr = new BinaryExpression(rhsExpr, BinaryExpression.Op.AND, new BinaryExpression(memberOfOp, BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr()));
                finalExprI = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.IMPLIES, rhsExpr), bdUnaryIntVar1, bdUnaryIntVar2, bdUnaryIntVar3);

                lhsExprII = new BinaryExpression(ternaryIntTupExpr, BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr());
                rhsExprII = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.DIVIDE, bdIntVar2Expr);                
                rhsExprII = new BinaryExpression(rhsExprII, BinaryExpression.Op.EQ, bdIntVar3Expr);
                rhsExprII = new BinaryExpression(rhsExprII, BinaryExpression.Op.AND, new BinaryExpression(exprUnaryTranslator.mkSingletonOutOfAtomExpr(bdIntVar2Expr), BinaryExpression.Op.EQ, new IntConstant(0)));                
                rhsExprII = new BinaryExpression(rhsExprII, BinaryExpression.Op.AND, new BinaryExpression(ternaryIntTupExpr, BinaryExpression.Op.EQ, memberOfOp));
                rhsExprII = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, rhsExprII, bdUnaryIntVar1, bdUnaryIntVar2, bdUnaryIntVar3);
                finalExprII = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExprII, BinaryExpression.Op.IMPLIES, rhsExprII), bdTernaryIntVar);
                break;

                case MOD:
                arithVarDecl = new ConstantDeclaration("MOD", translator.setOfTernaryIntSort);
                lhsExpr = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.MOD, bdIntVar2Expr);
                lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.EQ, bdIntVar3Expr);
                lhsExpr = new BinaryExpression(lhsExpr, BinaryExpression.Op.AND, new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(exprUnaryTranslator.mkSingletonOutOfAtomExpr(bdIntVar2Expr), BinaryExpression.Op.EQ, new IntConstant(0))));
                rhsExpr = new BinaryExpression(rhsExpr, BinaryExpression.Op.AND, new BinaryExpression(memberOfOp, BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr()));
                finalExprI = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExpr, BinaryExpression.Op.IMPLIES, rhsExpr), bdUnaryIntVar1, bdUnaryIntVar2, bdUnaryIntVar3);

                lhsExprII = new BinaryExpression(ternaryIntTupExpr, BinaryExpression.Op.MEMBER, arithVarDecl.getConstantExpr());
                rhsExprII = new BinaryExpression(bdIntVar1Expr, BinaryExpression.Op.MOD, bdIntVar2Expr);
                rhsExprII = new BinaryExpression(rhsExprII, BinaryExpression.Op.EQ, bdIntVar3Expr);
                rhsExprII = new BinaryExpression(rhsExprII, BinaryExpression.Op.AND, new BinaryExpression(exprUnaryTranslator.mkSingletonOutOfAtomExpr(bdIntVar2Expr), BinaryExpression.Op.EQ, new IntConstant(0)));
                rhsExprII = new BinaryExpression(rhsExprII, BinaryExpression.Op.AND, new BinaryExpression(ternaryIntTupExpr, BinaryExpression.Op.EQ, memberOfOp));
                rhsExprII = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, rhsExprII, bdUnaryIntVar1, bdUnaryIntVar2, bdUnaryIntVar3);
                finalExprII = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(lhsExprII, BinaryExpression.Op.EQ, rhsExprII), bdTernaryIntVar);
                break;
            default:
                break;                   
        }
        translator.smtProgram.addConstantDeclaration(arithVarDecl);
        translator.smtProgram.addAssertion(new Assertion("Arithmetic operator constant definition", finalExprI));
        translator.smtProgram.addAssertion(new Assertion("Arithmetic operator constant definition II", finalExprII));
        translator.arithOps.put(op, arithVarDecl.getConstantExpr());        
    }

    private Expression translateExprListToBinaryExpressions(BinaryExpression.Op op, ExprList exprList, Map<String, Expression> variablesScope)
    {

        if(exprList.args.size() == 0 )
        {
            if (op == BinaryExpression.Op.AND)
            {
                return new BooleanConstant(true);
            }

            if (op == BinaryExpression.Op.OR)
            {
                return new BooleanConstant(false);
            }
            throw new UnsupportedOperationException();
        }

        //ToDo: review the case of nested variable scopes
        Expression left         = translateExpr(exprList.args.get(0), variablesScope);

        if(exprList.args.size() == 1)
        {
            return left;
        }

        Expression right        = translateExpr(exprList.args.get(1), variablesScope);
        BinaryExpression result = new BinaryExpression(left, op, right);


        for(int i = 2; i < exprList.args.size(); i++)
        {
            Expression expr     = translateExpr(exprList.args.get(i), variablesScope);
            result              = new BinaryExpression(result, op, expr);
        }

        return result;
    }

    Expression translateExprQt(ExprQt exprQt, Map<String, Expression> variablesScope)
    {
        Map<String, List<VariableDeclaration>> quantifiedSingleton2AtomMap = new HashMap<>();
        Map<String, Expression> quantifiedVariable2ExpressionMap = new HashMap<>();
        LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap = new LinkedHashMap<>();

        Expression multiplicityConstraint = new BooleanConstant(true);
        
        for (Decl decl: exprQt.decls)
        {
            Expression declExpr     = getDeclarationExpr(decl, variablesScope);
            List<Sort> declSorts    = getExprSorts(decl.expr);

            if( decl.expr instanceof ExprUnary &&
                    ((ExprUnary) decl.expr).op != ExprUnary.Op.ONEOF)
            {
                Sort sort = declSorts.get(0).getSort();
                declSorts = declSorts.stream()
                        .map(s -> new SetSort(new TupleSort(s)))
                        .collect(Collectors.toList());

                String name = TranslatorUtils.sanitizeName(decl.get().label);
                VariableDeclaration variable = createVariable(declSorts.get(0), name);
                //ToDo: refactor this for set case
                quantifiedSingleton2AtomMap.put(name, new ArrayList<>(Collections.singletonList(variable)));
                variablesScope.put(decl.get().label, variable.getConstantExpr());
                quantifiedVariable2SignatureMap.put(decl.get().label, declExpr);
                quantifiedVariable2ExpressionMap.put(name, variable.getConstantExpr());

                switch (((ExprUnary) decl.expr).op)
                {
                    case SOMEOF:
                    {
                        multiplicityConstraint = new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(variable.getConstantExpr(), BinaryExpression.Op.EQ,
                            new UnaryExpression(UnaryExpression.Op.EMPTYSET, variable.getSort())
                            ));
                    } break;
                    case ONEOF:
                    {
                        VariableDeclaration multiplicityVariable = createVariable(sort, TranslatorUtils.getNewName());
                        quantifiedSingleton2AtomMap.get(name).add(multiplicityVariable);
                        multiplicityConstraint = new BinaryExpression(variable.getConstantExpr(), BinaryExpression.Op.EQ,
                                new UnaryExpression(UnaryExpression.Op.SINGLETON,
                                        new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, multiplicityVariable.getConstantExpr()))
                        );
                    } break;
                    case LONEOF:
                    {
                        VariableDeclaration multiplicityVariable = createVariable(sort, TranslatorUtils.getNewName());

                        quantifiedSingleton2AtomMap.get(name).add(multiplicityVariable);
                        multiplicityConstraint = new BinaryExpression(variable.getConstantExpr(), BinaryExpression.Op.SUBSET,
                                new UnaryExpression(UnaryExpression.Op.SINGLETON,
                                        new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, multiplicityVariable.getConstantExpr()))
                        );
                    } break;
                }
            }
            else
            {
                for (ExprHasName name : decl.names)
                {
                    Sort declExprSort = declSorts.get(0);
                    int arity = decl.expr.type().arity();
                    String sanBdVarName = TranslatorUtils.sanitizeName(name.label);

                    VariableDeclaration bdVarDecl = createVariable(declExprSort, sanBdVarName);
                    Expression bdVarTupleExpr = bdVarDecl.getConstantExpr();
                    List<VariableDeclaration> bdAtomVars = new ArrayList<>();

                    if (arity > 1) {
                        List<Expression> bdAtomExprs = new ArrayList<>();

                        for (int i = 0; i < arity; i++) {
                            Expression bdAtomVarExpr;
                            String varName = sanBdVarName + "_" + i;
                            VariableDeclaration bdAtomVar;

                            if (declSorts.get(i) instanceof IntSort) {
                                bdAtomVar = new VariableDeclaration(varName, translator.unaryIntTup);
                                bdAtomVarExpr = exprBinaryTranslator.mkTupleSelectExpr(exprUnaryTranslator.mkUnaryIntTupValue(bdAtomVar.getConstantExpr()), 0);
                            } else {
                                bdAtomVar = new VariableDeclaration(varName, translator.atomSort);
                                bdAtomVarExpr = bdAtomVar.getConstantExpr();
                            }
                            bdAtomVars.add(bdAtomVar);
                            bdAtomExprs.add(bdAtomVarExpr);
                        }
                        bdVarTupleExpr = exprUnaryTranslator.mkOneTupleExprOutofAtoms(bdAtomExprs);
                        quantifiedVariable2ExpressionMap.put(sanBdVarName, bdVarTupleExpr);
                        quantifiedSingleton2AtomMap.put(sanBdVarName, bdAtomVars);
                    } else {
                        bdAtomVars.add(bdVarDecl);
                        if ((declExprSort instanceof IntSort)) {
                            bdVarTupleExpr = exprUnaryTranslator.mkUnaryIntTupValue(bdVarDecl.getConstantExpr());
                        } else {
                            bdVarTupleExpr = exprUnaryTranslator.mkOneTupleExprOutofAtoms(bdVarTupleExpr);
                        }
                        quantifiedVariable2ExpressionMap.put(sanBdVarName, bdVarTupleExpr);
                        quantifiedSingleton2AtomMap.put(sanBdVarName, bdAtomVars);
                    }

                    variablesScope.put(name.label, mkSingletonOutOfTuple(bdVarTupleExpr));
                    quantifiedVariable2SignatureMap.put(sanBdVarName, declExpr);
                }
            }
        }
        
        // Translate quantified expression body
        Expression bodyExpr = translateExpr(exprQt.sub, variablesScope);

        switch (exprQt.op)
        {
            case ALL    : return  translateAllQuantifier(quantifiedVariable2SignatureMap, quantifiedSingleton2AtomMap, quantifiedVariable2ExpressionMap, bodyExpr, multiplicityConstraint);
            case SOME   : return  translateSomeQuantifier(quantifiedVariable2SignatureMap, quantifiedSingleton2AtomMap, quantifiedVariable2ExpressionMap, bodyExpr, multiplicityConstraint);
            case NO     : return  translateNoQuantifier(quantifiedVariable2SignatureMap, quantifiedSingleton2AtomMap, quantifiedVariable2ExpressionMap, bodyExpr, multiplicityConstraint);
            case LONE   : {
                Map<String, List<VariableDeclaration>>         sndBdVarNameTobdAtomVars    = new HashMap<>();
                Map<String, Expression>                             sndBdVarNameToTupleExpr     = new HashMap<>();
                LinkedHashMap<String, Expression>                   sndBdVarNameToExprMap       = new LinkedHashMap<>(); 
                
                Expression sndBodyExpr = createSndSetBdvarsAndExpr(sndBdVarNameToExprMap, sndBdVarNameTobdAtomVars, sndBdVarNameToTupleExpr, variablesScope, exprQt);
              
                return  translateLoneQuantifier(quantifiedVariable2SignatureMap, sndBdVarNameToExprMap, quantifiedSingleton2AtomMap, sndBdVarNameTobdAtomVars,
                                                quantifiedVariable2ExpressionMap, sndBdVarNameToTupleExpr, bodyExpr, sndBodyExpr, multiplicityConstraint);
            }
            case ONE    : {
                Map<String, List<VariableDeclaration>>         sndBdVarNameTobdAtomVars    = new HashMap<>();
                Map<String, Expression>                             sndBdVarNameToTupleExpr     = new HashMap<>();
                LinkedHashMap<String, Expression>                   sndBdVarNameToExprMap       = new LinkedHashMap<>(); 
                
                Expression sndBodyExpr = createSndSetBdvarsAndExpr(sndBdVarNameToExprMap, sndBdVarNameTobdAtomVars, sndBdVarNameToTupleExpr, variablesScope, exprQt);
                           
                return  translateOneQuantifier(quantifiedVariable2SignatureMap, sndBdVarNameToExprMap, quantifiedSingleton2AtomMap, sndBdVarNameTobdAtomVars,
                                               quantifiedVariable2ExpressionMap, sndBdVarNameToTupleExpr, bodyExpr, sndBodyExpr, multiplicityConstraint);
            }
            case COMPREHENSION :
            {
                List<Sort> elementSorts     = new ArrayList<>();
                
                for(int i = 0; i < exprQt.decls.size(); ++i)
                {                    
                    for(int j = 0; j < exprQt.decls.get(i).names.size(); ++j)
                    {
                        elementSorts.addAll(getExprSorts(exprQt.decls.get(i).expr));
                    }                    
                }
                
                String              setBdVarName    = TranslatorUtils.getNewSetName();
                SetSort             setSort         = new SetSort(new TupleSort(elementSorts));
                VariableDeclaration setBdVar   = new VariableDeclaration(setBdVarName, setSort);
                LinkedHashMap<VariableDeclaration, Expression> bdVars = new LinkedHashMap<>();
                
                for(Decl decl : exprQt.decls)
                {                    
                    Expression declExpr         = getDeclarationExpr(decl, variablesScope);
                    List<Sort> declExprSorts    = getExprSorts(decl.expr);

                    for (ExprHasName name: decl.names)
                    {
                        String sanitizedName = TranslatorUtils.sanitizeName(name.label);
                        VariableDeclaration bdVar = new VariableDeclaration(sanitizedName, declExprSorts.get(0));
                        variablesScope.put(name.label, bdVar.getConstantExpr());
                        bdVars.put(bdVar, declExpr);
                    }                    
                }
                Expression setCompBodyExpr  = translateExpr(exprQt.sub, variablesScope);
                Expression membership       = getMemberExpression(bdVars, 0);
                
                for(int i = 1; i < bdVars.size(); ++i)
                {
                    membership = new BinaryExpression(membership, BinaryExpression.Op.AND, getMemberExpression(bdVars, i));
                }
                membership = new BinaryExpression(membership, BinaryExpression.Op.AND, setCompBodyExpr);
                Expression setMembership = new BinaryExpression(exprUnaryTranslator.mkTupleExpr(new ArrayList<>(bdVars.keySet())), BinaryExpression.Op.MEMBER, setBdVar.getConstantExpr());
                membership = new BinaryExpression(membership, BinaryExpression.Op.EQ, setMembership);
                Expression forallExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new ArrayList<>(bdVars.keySet()), membership);
                
                if(translator.auxExpr != null)
                {                    
                    translator.auxExpr = new BinaryExpression(translator.auxExpr, BinaryExpression.Op.AND, forallExpr);
                }
                else
                {
                    translator.auxExpr = forallExpr;
                }
                
                translator.existentialBdVars.add(setBdVar);
                return setBdVar.getConstantExpr();
            }
            default: throw new UnsupportedOperationException();
        }
    }
    
    private Expression createSndSetBdvarsAndExpr(LinkedHashMap<String, Expression> bdVarToExprMap, 
                                                 Map<String, List<VariableDeclaration>> bdTupVarNameTobdAtomVars,
                                                 Map<String, Expression> bdTupVarNameToTupleExpr, 
                                                 Map<String, Expression> variablesScope, ExprQt exprQt)
    {        
        for (Decl decl: exprQt.decls)
        {
            Expression declExpr     = getDeclarationExpr(decl, variablesScope);
            List<Sort> declSorts    = getExprSorts(decl.expr);            
            
            for (ExprHasName name: decl.names)
            {
                Sort    declExprSort    = declSorts.get(0);
                int     arity           = decl.expr.type().arity();
                String  sanBdVarName    = TranslatorUtils.sanitizeName(name.label);
                
                VariableDeclaration bdVarDecl = createVariable(declExprSort, sanBdVarName);
                Expression bdVarTupleExpr = bdVarDecl.getConstantExpr();
                List<VariableDeclaration>  bdAtomVars    = new ArrayList<>();
                
                if(arity > 1)
                {                                                       
                    List<Expression> bdAtomExprs   = new ArrayList<>();                    
                    for(int i = 0; i < arity; i++)
                    {
                        Expression bdAtomVarExpr;
                        String varName = sanBdVarName+"_"+i+"_2";
                        VariableDeclaration bdAtomVar;
                                                
                        if(declSorts.get(i) instanceof IntSort)
                        {
                            bdAtomVar = new VariableDeclaration(varName, translator.unaryIntTup);
                            bdAtomVarExpr = exprBinaryTranslator.mkTupleSelectExpr(exprUnaryTranslator.mkUnaryIntTupValue(bdAtomVar.getConstantExpr()), 0);
                        }
                        else
                        {
                            bdAtomVar = new VariableDeclaration(varName, translator.atomSort);
                            bdAtomVarExpr = bdAtomVar.getConstantExpr();
                        } 
                        bdAtomVars.add(bdAtomVar);
                        bdAtomExprs.add(bdAtomVarExpr);
                    }
                    bdVarTupleExpr = exprUnaryTranslator.mkOneTupleExprOutofAtoms(bdAtomExprs);
                    bdTupVarNameToTupleExpr.put(sanBdVarName, bdVarTupleExpr);
                    bdTupVarNameTobdAtomVars.put(sanBdVarName, bdAtomVars);
                }
                else
                {
                    bdAtomVars.add(bdVarDecl);
                    if((declExprSort instanceof IntSort))
                    {
                        bdVarTupleExpr = exprUnaryTranslator.mkUnaryIntTupValue(bdVarDecl.getConstantExpr());
                    }
                    else
                    {
                        bdVarTupleExpr = exprUnaryTranslator.mkOneTupleExprOutofAtoms(bdVarTupleExpr);
                    }  
                    bdTupVarNameToTupleExpr.put(sanBdVarName, bdVarTupleExpr);
                    bdTupVarNameTobdAtomVars.put(sanBdVarName, bdAtomVars);                    
                }                
                variablesScope.put(name.label, mkSingletonOutOfTuple(bdVarTupleExpr));
                bdVarToExprMap.put(sanBdVarName, declExpr);
            }
        }
        
        // Translate quantified expression body
        return translateExpr(exprQt.sub, variablesScope);        
    }
    
    // (all e: R|not P) or (some e : R | P and all e2 : R | not(e = e2) => not P)
    private Expression translateLoneQuantifier(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, LinkedHashMap<String, Expression> sndBdVarToExprMap,
                                               Map<String, List<VariableDeclaration>> bdVarNameTobdAtomVars, Map<String, List<VariableDeclaration>> sndBdVarNameTobdAtomVars,
                                               Map<String, Expression> bdVarNameToTupleExpr, Map<String, Expression> sndBdVarNameToTupleExpr,
                                               Expression bodyExpr, Expression sndBodyExpr, Expression multiplicityConstraint)
    {
        Expression fstPartBodyExpr = bodyExpr;
        Expression sndPartBodyExpr = bodyExpr;
        Expression thdPartBodyExpr = sndBodyExpr;

        // (all e: R|not P) 
        List<VariableDeclaration> fstBdVars = new ArrayList<>();
        for(List<VariableDeclaration> bdVars : bdVarNameTobdAtomVars.values())
        {
            fstBdVars.addAll(bdVars);
        }
        Expression fstMembership = getConstraints(quantifiedVariable2SignatureMap, bdVarNameToTupleExpr, multiplicityConstraint);
        Expression fstBodyExpr = new BinaryExpression(fstMembership, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, bodyExpr));
        QuantifiedExpression fstQuantExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, fstBdVars, fstBodyExpr);
        
        // some e1 : R | P
        Expression sndExistExpr = new BinaryExpression(fstMembership, BinaryExpression.Op.AND, sndPartBodyExpr);
        
        // Membership constraints of the universal constraints all e2 : R | not(e1 = e2) => not P)              
        // all e2 : R
        
        List<VariableDeclaration> sndBdVars = new ArrayList<>();
        for(List<VariableDeclaration> bdVars : sndBdVarNameTobdAtomVars.values())
        {
            sndBdVars.addAll(bdVars);
        }
        
        // all e2 : R | not(e1 = e2) => not P
        Expression distExpr = getConstraints(sndBdVarToExprMap, sndBdVarNameToTupleExpr, multiplicityConstraint);
        
        for(Map.Entry<String, Expression> varNameToExpr : bdVarNameToTupleExpr.entrySet())
        {
            Expression fstExpr = varNameToExpr.getValue();
            Expression sndExpr = sndBdVarNameToTupleExpr.get(varNameToExpr.getKey());
            distExpr = new BinaryExpression(distExpr, BinaryExpression.Op.AND, new MultiArityExpression(MultiArityExpression.Op.DISTINCT, fstExpr, sndExpr));
        }
        distExpr = new BinaryExpression(distExpr, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, thdPartBodyExpr));
        QuantifiedExpression sndForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, sndBdVars, distExpr);
        // (some e : R | P and all e2 : R | not(e = e2) => not P)
        QuantifiedExpression existFormula = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, fstBdVars, new BinaryExpression(sndExistExpr, BinaryExpression.Op.AND, sndForall));
        
        return new BinaryExpression(fstQuantExpr, BinaryExpression.Op.OR, existFormula);
    }   
    
    // (some e : R | P and all e2 : R | not(e = e2) => not P)
    private Expression translateOneQuantifier(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, LinkedHashMap<String, Expression> sndBdVarToExprMap,
                                              Map<String, List<VariableDeclaration>> bdVarNameTobdAtomVars, Map<String, List<VariableDeclaration>> sndBdVarNameTobdAtomVars,
                                              Map<String, Expression> bdVarNameToTupleExpr, Map<String, Expression> sndBdVarNameToTupleExpr,
                                              Expression bodyExpr, Expression sndBodyExpr,
                                              Expression multiplicityConstraint)
    {
        Expression fstPartBodyExpr = bodyExpr;
        Expression sndPartBodyExpr = bodyExpr;
        Expression thdPartBodyExpr = sndBodyExpr;

        // (all e: R|not P) 
        List<VariableDeclaration> fstBdVars = new ArrayList<>();
        
        for(List<VariableDeclaration> bdVars : bdVarNameTobdAtomVars.values())
        {
            fstBdVars.addAll(bdVars);
        }
        Expression fstMembership = getConstraints(quantifiedVariable2SignatureMap, bdVarNameToTupleExpr, multiplicityConstraint);

        // some e1 : R | P
        Expression sndExistExpr = new BinaryExpression(fstMembership, BinaryExpression.Op.AND, sndPartBodyExpr);
        
        // Membership constraints of the universal constraints all e2 : R | not(e1 = e2) => not P)              
        // all e2 : R
        
        List<VariableDeclaration> sndBdVars = new ArrayList<>();
        for(List<VariableDeclaration> bdVars : sndBdVarNameTobdAtomVars.values())
        {
            sndBdVars.addAll(bdVars);
        }
        
        // all e2 : R | not(e1 = e2) => not P
        Expression distExpr = getConstraints(sndBdVarToExprMap, sndBdVarNameToTupleExpr, multiplicityConstraint);
        
        for(Map.Entry<String, Expression> varNameToExpr : bdVarNameToTupleExpr.entrySet())
        {
            Expression fstExpr = varNameToExpr.getValue();
            Expression sndExpr = sndBdVarNameToTupleExpr.get(varNameToExpr.getKey());
            distExpr = new BinaryExpression(distExpr, BinaryExpression.Op.AND, new MultiArityExpression(MultiArityExpression.Op.DISTINCT, fstExpr, sndExpr));
        }
        distExpr = new BinaryExpression(distExpr, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, thdPartBodyExpr));
        QuantifiedExpression sndForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, sndBdVars, distExpr);
        // (some e : R | P and all e2 : R | not(e = e2) => not P)
        QuantifiedExpression existFormula = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, fstBdVars, new BinaryExpression(sndExistExpr, BinaryExpression.Op.AND, sndForall));
        
        return existFormula;
    }       
    
    private QuantifiedExpression translateNoQuantifier(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, Map<String, List<VariableDeclaration>> bdTupVarNameTobdAtomVars, Map<String, Expression> bdTupVarNameToTupleExpr, Expression bodyExpr,
                                                       Expression multiplicityConstraint)
    {
        List<VariableDeclaration> bdVars = new ArrayList<>();
        Expression membership = getConstraints(quantifiedVariable2SignatureMap, bdTupVarNameToTupleExpr, multiplicityConstraint);
        bodyExpr = new BinaryExpression(membership, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, bodyExpr));
        for(List<VariableDeclaration> vars : bdTupVarNameTobdAtomVars.values())
        {
            bdVars.addAll(vars);
        }        
        QuantifiedExpression quantifiedExpression = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, bdVars, bodyExpr);
        return quantifiedExpression;     
    }
    
    private Expression getConstraints(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, Map<String, Expression> quantifiedVariable2ExpressionMap, Expression multiplicityConstraint)
    {
        Expression constraint = new BooleanConstant(true);
        
        for(Map.Entry<String, Expression> entry : quantifiedVariable2SignatureMap.entrySet())
        {
            String      name            = entry.getKey();
            Expression  setExpression   = entry.getValue();
            Expression  quantifiedVariableExpression   = quantifiedVariable2ExpressionMap.get(name);

            // add constraint (member (mkTuple x) A) for x: A
            if(quantifiedVariableExpression.getSort() instanceof TupleSort)
            {
                constraint = new BinaryExpression(constraint, BinaryExpression.Op.AND,
                        new BinaryExpression(quantifiedVariableExpression, BinaryExpression.Op.MEMBER, setExpression));
            }
            else // add constraint (subset x A) for x: set A (or lone A, some A)
            {
                constraint = new BinaryExpression(constraint, BinaryExpression.Op.AND,
                        new BinaryExpression(quantifiedVariableExpression, BinaryExpression.Op.SUBSET, setExpression));

            }
        }
        constraint = new BinaryExpression(multiplicityConstraint, BinaryExpression.Op.AND, constraint);
        return constraint;
    }

    private QuantifiedExpression translateAllQuantifier(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, Map<String, List<VariableDeclaration>> bdTupVarNameTobdAtomVars, Map<String, Expression> bdTupVarNameToTupleExpr, Expression bodyExpr,
                                                        Expression multiplicityConstraint)
    {
        List<VariableDeclaration> bdVars = new ArrayList<>();
        Expression membership = getConstraints(quantifiedVariable2SignatureMap, bdTupVarNameToTupleExpr, multiplicityConstraint);
        bodyExpr = new BinaryExpression(membership, BinaryExpression.Op.IMPLIES, bodyExpr);
        for(List<VariableDeclaration> vars : bdTupVarNameTobdAtomVars.values())
        {
            bdVars.addAll(vars);
        }        
        QuantifiedExpression quantifiedExpression = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, bdVars, bodyExpr);
        return quantifiedExpression;
    }

    private QuantifiedExpression translateSomeQuantifier(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, Map<String, List<VariableDeclaration>> quantifiedSingleton2AtomMap, Map<String, Expression> quantifiedVariable2ExpressionMap, Expression bodyExpr, Expression multiplicityConstraint)
    {
        List<VariableDeclaration> bdVars = new ArrayList<>();
        Expression membership = getConstraints(quantifiedVariable2SignatureMap, quantifiedVariable2ExpressionMap, multiplicityConstraint);
        bodyExpr = new BinaryExpression(membership, BinaryExpression.Op.AND, bodyExpr);
        for(List<VariableDeclaration> vars : quantifiedSingleton2AtomMap.values())
        {
            bdVars.addAll(vars);
        }        
        QuantifiedExpression quantifiedExpression = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, bdVars, bodyExpr);
        return quantifiedExpression;
    }


    public BinaryExpression getMemberExpression(Map<VariableDeclaration, Expression> bdVarToExprMap, int index)
    {
        VariableDeclaration bdVar           = (new ArrayList<>(bdVarToExprMap.keySet())).get(index);
        Expression                  bdVarParExpr    = bdVarToExprMap.get(bdVar);
        Expression                  tupleExpr       = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, bdVar.getConstantExpr());
        
        if((bdVar.getSort() instanceof UninterpretedSort) || (bdVar.getSort() instanceof IntSort))
        {
            tupleExpr = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, bdVar.getConstantExpr());
        }
        else if(bdVar.getSort() instanceof TupleSort)
        {
            tupleExpr = bdVar.getConstantExpr();
        }
        else if(bdVar.getSort() instanceof SetSort)
        {
            return new BinaryExpression(bdVar.getConstantExpr(), BinaryExpression.Op.SUBSET, bdVarParExpr);
        }
        return new BinaryExpression(tupleExpr, BinaryExpression.Op.MEMBER, bdVarParExpr);
    }

    public Expression getDeclarationExpr(Decl decl, Map<String, Expression> variablesScope)
    {
        return translateExpr(decl.expr, variablesScope);
    }
    
    
    /**
     * Auxiliary functions
     */
        
    List<VariableDeclaration> getBdVars(Sort sort, int num)
    {
        List<VariableDeclaration> bdVars = new ArrayList<>();
        
        for(int i = 0; i < num; i++)
        {
            bdVars.add(new VariableDeclaration(TranslatorUtils.getNewAtomName(), sort));
        }
        return bdVars;
    }
    
    VariableDeclaration createVariable(Sort sort, String name)
    {
        if(sort instanceof IntSort)
        {
            return new VariableDeclaration(name, translator.unaryIntTup);
        }
        return new VariableDeclaration(name, sort);
    }

    List<Sort> getExprSorts(Expr expr)
    {
        List<Sort> sorts = new ArrayList<>();
        for(List<PrimSig> sigs : expr.type().fold())
        {
            for(PrimSig s : sigs)
            {
                if(s.type().is_int())
                {
                    sorts.add(translator.intSort);
                }
                else
                {
                    sorts.add(translator.atomSort);
                }
            }
        }
        return sorts;
    }
    
    List<VariableDeclaration> getBdTupleVars(List<Sort> sorts, int arity, int num)
    {
        List<Sort> elementSorts = new ArrayList<>();
        List<VariableDeclaration> bdVars = new ArrayList<>();
        
        for(int i = 0; i < arity; i++)
        {
            elementSorts.add(sorts.get(i));
        }
        for(int i = 0; i < num; i++)
        {
            bdVars.add(new VariableDeclaration(TranslatorUtils.getNewAtomName(), new TupleSort(elementSorts)));
        }
        return bdVars;
    }    

    Expression mkSingletonOutOfTupleOrAtom(ConstantExpression constantExpression)
    {
        UnaryExpression singleton = null;
        
        if((constantExpression.getDeclaration().getSort() instanceof UninterpretedSort) ||
                constantExpression.getDeclaration().getSort() instanceof IntSort)
        {
            MultiArityExpression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constantExpression);
            singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);            
        }
        else if(constantExpression.getDeclaration().getSort() instanceof TupleSort)
        {
            singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, constantExpression);  
        }
        else
        {
            throw new UnsupportedOperationException("Unexpected!");
        }
        return singleton;
    }
    
    
    
    Expression mkSingletonOutOfAtoms(List<Expression> atomExprs)
    {
        MultiArityExpression tuple      = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, atomExprs);
        UnaryExpression      singleton  = new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);
        return singleton;
    }
    
    Expression mkSingletonOutOfTuple(Expression tupleExpr)
    {
        UnaryExpression      singleton  = new UnaryExpression(UnaryExpression.Op.SINGLETON, tupleExpr);
        return singleton;
    }    
    
    Expression mkEmptyRelationOfSort(List<Sort> sorts) 
    {
        if(sorts.isEmpty())
        {
            try {
                throw new Exception("Unexpected: sorts is empty!");
            } catch (Exception ex) {
                Logger.getLogger(ExprTranslator.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
        return new UnaryExpression(UnaryExpression.Op.EMPTYSET, new SetSort(new TupleSort(sorts)));
    }

    Expression mkUnaryRelationOutOfAtomsOrTuples(List<Expression> atomOrTupleExprs)
    {
        List<Expression> atomTupleExprs = new ArrayList<>();
        
        for(Expression e : atomOrTupleExprs)
        {
            if(e instanceof ConstantExpression)
            {
                if(((ConstantExpression)e).getDeclaration().getSort() == translator.atomSort || 
                        ((ConstantExpression)e).getDeclaration().getSort() == translator.intSort)
                {
                    MultiArityExpression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, e);
                    atomTupleExprs.add(tuple);                    
                }
                else if(((ConstantExpression)e).getDeclaration().getSort() instanceof TupleSort)
                {
                    atomTupleExprs.add(e);
                }
                else
                {
                    throw new UnsupportedOperationException("Something is wrong here!");
                }
            }
            else
            {
                atomTupleExprs.add(e);
            }
        }
        
        
        UnaryExpression singleton  = new UnaryExpression(UnaryExpression.Op.SINGLETON, atomTupleExprs.get(0));
        
        if(atomTupleExprs.size() > 1)
        {
            atomTupleExprs.remove(0);
            atomTupleExprs.add(singleton);
            MultiArityExpression set = new MultiArityExpression(MultiArityExpression.Op.INSERT, atomTupleExprs);            
            return set;
        }
        return singleton;
    }       
}
