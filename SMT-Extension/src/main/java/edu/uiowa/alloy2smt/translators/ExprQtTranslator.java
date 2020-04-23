package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.*;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.*;
import java.util.stream.Collectors;

public class ExprQtTranslator
{
  final ExprTranslator exprTranslator;
  final ExprUnaryTranslator exprUnaryTranslator;
  final ExprBinaryTranslator exprBinaryTranslator;
  final Alloy2SmtTranslator translator;

  public ExprQtTranslator(ExprTranslator exprTranslator)
  {
    this.exprTranslator = exprTranslator;
    this.exprUnaryTranslator = exprTranslator.exprUnaryTranslator;
    this.exprBinaryTranslator = exprTranslator.exprBinaryTranslator;
    this.translator = exprTranslator.translator;
  }

  SmtExpr translateExprQt(ExprQt exprQt, Environment environment)
  {
    // create a new scope for quantified variables
    Environment newEnvironment = new Environment(environment);
    List<SmtVariable> smtVariables = exprTranslator.translateDecls(exprQt.decls, newEnvironment);
    SmtExpr constraints = getDisjointConstraints(exprQt, newEnvironment);

    // translate the body of the quantified expression
    SmtExpr body = exprTranslator.translateExpr(exprQt.sub, newEnvironment);
    switch (exprQt.op)
    {
      case ALL:
        return translateAllQuantifier(body, smtVariables, newEnvironment, constraints);
      case NO:
        return translateNoQuantifier(body, smtVariables, newEnvironment, constraints);
      case SOME:
        return translateSomeQuantifier(body, smtVariables, newEnvironment, constraints);
      case ONE:
        return translateOneQuantifier(body, smtVariables, newEnvironment, constraints);
      case LONE:
        return translateLoneQuantifier(body, smtVariables, newEnvironment, constraints);
      case COMPREHENSION:
        return translateComprehension(exprQt, body, smtVariables, newEnvironment);
      default:
        throw new UnsupportedOperationException();
    }
  }

  private SmtExpr getDisjointConstraints(ExprQt exprQt, Environment environment)
  {
    SmtExpr disjointConstraints = BoolConstant.True;

    for (Decl decl : exprQt.decls)
    {
      // disjoint fields
      if (decl.disjoint != null && decl.names.size() > 1)
      {
        for (int i = 0; i < decl.names.size() - 1; i++)
        {
          for (int j = i + 1; j < decl.names.size(); j++)
          {
            SmtExpr variableI = environment.get(decl.names.get(i).label);
            SmtExpr variableJ = environment.get(decl.names.get(j).label);

            if (variableJ.getSort() instanceof UninterpretedSort)
            {
              throw new UnsupportedOperationException();
            }

            if (variableJ.getSort() instanceof TupleSort)
            {
              variableI = SmtUnaryExpr.Op.SINGLETON.make(variableI);
              variableJ = SmtUnaryExpr.Op.SINGLETON.make(variableJ);
            }

            SmtExpr intersect = SmtBinaryExpr.Op.INTERSECTION.make(variableI, variableJ);
            SmtExpr emptySet = SmtUnaryExpr.Op.EMPTYSET.make(variableI.getSort());
            SmtExpr equal = SmtBinaryExpr.Op.EQ.make(intersect, emptySet);
            disjointConstraints = SmtMultiArityExpr.Op.AND.make(disjointConstraints, equal);
          }
        }
      }
    }
    return disjointConstraints;
  }

  private SmtExpr translateComprehension(ExprQt exprQt, SmtExpr body, List<SmtVariable> smtVariables, Environment environment)
  {
    // {x: e1, y: e2, ... | f} is translated into
    // declare-fun comprehension(freeVariables): (e1 product e2 product ...)
    // assert forall x, y,... (x in e1 and y in e2 ... and f <=>
    // (x, y, ...) in comprehension(freeVariables))

    // determine the sort of the alloy comprehension
    List<Sort> elementSorts = new ArrayList<>();
    for (SmtVariable smtVariable : smtVariables)
    {
      // all variables should be unary
      assert (smtVariable.getSort() instanceof TupleSort);
      TupleSort tupleSort = (TupleSort) smtVariable.getSort();
      elementSorts.add(tupleSort.elementSorts.get(0));
    }
    Sort returnSort = new SetSort(new TupleSort(elementSorts));

    // determine the free variables for the set comprehension from the environment, and
    // add theme as arguments to the comprehension function
    LinkedHashMap<String, SmtExpr> argumentsMap = environment.getParent().getVariables();
    List<Sort> argumentSorts = new ArrayList<>();
    List<SmtExpr> arguments = new ArrayList<>();
    List<SmtVariable> quantifiedArguments = new ArrayList<>();
    for (Map.Entry<String, SmtExpr> argument : argumentsMap.entrySet())
    {
      Variable variable = (Variable) argument.getValue();
      // add the variable as an argument to the call expression
      arguments.add(variable);
      Sort sort = variable.getSort();
      // add the sort of the variable to the declaration of the comprehension function
      argumentSorts.add(sort);
      quantifiedArguments.add((SmtVariable) variable.getDeclaration());
    }

    FunctionDeclaration setFunction = new FunctionDeclaration(TranslatorUtils.getFreshName(returnSort), argumentSorts, returnSort, false);
    translator.smtScript.addFunction(setFunction);

    SmtExpr smtCallExpr;
    if (argumentSorts.size() == 0)
    {
      smtCallExpr = setFunction.getVariable();
    }
    else
    {
      List<SmtExpr> smtExprs = AlloyUtils.getFunctionCallArguments(quantifiedArguments, argumentsMap);
      smtCallExpr = new SmtCallExpr(setFunction, smtExprs);
    }

    SmtExpr membership = getMemberOrSubsetExpressions(smtVariables);

    List<SmtExpr> quantifiedSmtExprs = smtVariables.stream()
                                                   .map(v -> SmtBinaryExpr.Op.TUPSEL.make(IntConstant.getInstance(0), v.getVariable()))
                                                   .collect(Collectors.toList());

    SmtExpr tuple = SmtMultiArityExpr.Op.MKTUPLE.make(quantifiedSmtExprs);

    SmtExpr tupleMember = SmtBinaryExpr.Op.MEMBER.make(tuple, smtCallExpr);

    SmtExpr and = SmtMultiArityExpr.Op.AND.make(membership, body);

    SmtExpr equivalence = SmtBinaryExpr.Op.EQ.make(tupleMember, and);

    // add variables defined in functions, predicates or let expression to the list of quantifiers
    quantifiedArguments.addAll(smtVariables);
    SmtExpr forAll = SmtQtExpr.Op.FORALL.make(equivalence, quantifiedArguments);

    Assertion assertion = AlloyUtils.getAssertion(Collections.singletonList(exprQt.pos),
        setFunction.getName() + " = " + exprQt.toString(), forAll);
    translator.smtScript.addAssertion(assertion);

    if (argumentSorts.size() == 0)
    {
      return setFunction.getVariable();
    }
    else
    {
      return new SmtCallExpr(setFunction, arguments);
    }
  }


  private SmtVariable getVariableDeclaration(Expr expr, String variableName, SetSort setSort, SmtExpr range)
  {
    if (expr instanceof Sig)
    {
      return getVariableDeclaration(variableName, setSort, range);
    }
    if (expr instanceof ExprUnary)
    {
      ExprUnary.Op multiplicityOperator = ((ExprUnary) expr).op;
      switch (multiplicityOperator)
      {

        case ONEOF:
        {
          return getVariableDeclaration(variableName, setSort, range);
        }
        case SOMEOF: // same as SETOF
        case LONEOF: // same as SETOF
        case NOOP: // only happens with relations
        case SETOF:
        {
          SmtVariable declaration = new SmtVariable(variableName, setSort, true);
          SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(declaration.getVariable(), range);
          declaration.setConstraint(subset);
          return declaration;
        }
        default:
          throw new UnsupportedOperationException();
      }
    }
    if (expr instanceof ExprBinary)
    {
      ExprBinary.Op multiplicityOperator = ((ExprBinary) expr).op;
      switch (multiplicityOperator)
      {
        case ARROW:
        case ANY_ARROW_SOME:
        case ANY_ARROW_ONE:
        case ANY_ARROW_LONE:
        case SOME_ARROW_ANY:
        case SOME_ARROW_SOME:
        case SOME_ARROW_ONE:
        case SOME_ARROW_LONE:
        case ONE_ARROW_ANY:
        case ONE_ARROW_SOME:
        case ONE_ARROW_ONE:
        case ONE_ARROW_LONE:
        case LONE_ARROW_ANY:
        case LONE_ARROW_SOME:
        case LONE_ARROW_ONE:
        case LONE_ARROW_LONE:
        {
          SmtVariable declaration = new SmtVariable(variableName, setSort, true);
          SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(declaration.getVariable(), range);
          declaration.setConstraint(subset);
          return declaration;
        }
        default:
          throw new UnsupportedOperationException();
      }
    }
    throw new UnsupportedOperationException();
  }

  private SmtVariable getVariableDeclaration(String variableName, SetSort setSort, SmtExpr range)
  {
    SmtVariable declaration = new SmtVariable(variableName, setSort.elementSort, true);
    SmtExpr member = SmtBinaryExpr.Op.MEMBER.make(declaration.getVariable(), range);
    declaration.setConstraint(member);
    return declaration;
  }

  private SmtExpr getMultiplicityConstraint(Expr expr, SmtVariable variable, SetSort setSort)
  {
    if (expr instanceof ExprUnary)
    {
      ExprUnary.Op multiplicityOperator = ((ExprUnary) expr).op;
      SmtExpr emptySet = SmtUnaryExpr.Op.EMPTYSET.make(setSort);
      switch (multiplicityOperator)
      {
        case NOOP: // same as ONEOF
        case ONEOF:
        {
          // variable.getSort() is a tuple sort, so there is no constraint
          return BoolConstant.True;
        }
        case SOMEOF:
        {
          // the set is not empty
          SmtExpr empty = SmtBinaryExpr.Op.EQ.make(variable.getVariable(), emptySet);
          SmtExpr notEmpty = SmtUnaryExpr.Op.NOT.make(empty);
          return notEmpty;
        }
        case SETOF:
        {
          // variable.getSort() is a set, so there is no constraint
          return BoolConstant.True;
        }
        case LONEOF:
        {
          // either the set is empty or a singleton
          SmtExpr empty = SmtBinaryExpr.Op.EQ.make(variable.getVariable(), emptySet);
          SmtVariable singleElement = new SmtVariable(TranslatorUtils.getFreshName(setSort.elementSort), setSort.elementSort, false);
          SmtExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(singleElement.getVariable());
          SmtExpr isSingleton = SmtBinaryExpr.Op.EQ.make(variable.getVariable(), singleton);
          SmtExpr emptyOrSingleton = SmtMultiArityExpr.Op.OR.make(empty, isSingleton);
          SmtExpr exists = SmtQtExpr.Op.EXISTS.make(emptyOrSingleton, singleElement);
          return exists;
        }
        default:
          throw new UnsupportedOperationException();
      }
    }
    if (expr instanceof ExprBinary)
    {
      return BoolConstant.True;
    }
    throw new UnsupportedOperationException();
  }

  private SmtExpr translateAllQuantifier(SmtExpr body, List<SmtVariable> smtVariables,
                                         Environment environment, SmtExpr constraints)
  {
    // all x: e1, y: e2, ... | f is translated into
    // forall x, y,... (x in e1 and y in e2 and ... and constraints implies f)


    SmtExpr multiplicity = getMemberOrSubsetExpressions(smtVariables);
    SmtExpr and = SmtMultiArityExpr.Op.AND.make(multiplicity, constraints);
    SmtQtExpr exists = environment.getAuxiliaryFormula();

    if (exists != null)
    {
      SmtExpr and2 = SmtMultiArityExpr.Op.AND.make(exists.getExpression(), and);
      exists = SmtQtExpr.Op.EXISTS.make(and2, exists.getVariables());
      environment.clearAuxiliaryFormula();
    }

    body = SmtBinaryExpr.Op.IMPLIES.make(exists, body);
    SmtExpr forAll = SmtQtExpr.Op.FORALL.make(body, smtVariables);

    SmtExpr translation = exprTranslator.translateAuxiliaryFormula(forAll, environment);
    return translation;
  }

  private SmtExpr translateNoQuantifier(SmtExpr body, List<SmtVariable> smtVariables,
                                        Environment environment, SmtExpr multiplicityConstraints)
  {
    SmtExpr notBody = SmtUnaryExpr.Op.NOT.make(body);
    return translateAllQuantifier(notBody, smtVariables, environment, multiplicityConstraints);
  }

  private SmtExpr translateSomeQuantifier(SmtExpr body, List<SmtVariable> smtVariables,
                                          Environment environment, SmtExpr constraints)
  {

    // some x: e1, y: e2, ... | f is translated into
    // exists x, y,... (x in e1 and y in e2 and ... and constraints and f)

    SmtExpr multiplicity = getMemberOrSubsetExpressions(smtVariables);
    SmtMultiArityExpr and = SmtMultiArityExpr.Op.AND.make(multiplicity, constraints);

    SmtQtExpr existsSet = environment.getAuxiliaryFormula();
    if (existsSet != null)
    {
      List<SmtExpr> smtExprs = new ArrayList<>(and.getExpressions());
      smtExprs.add(existsSet.getExpression());
      and = SmtMultiArityExpr.Op.AND.make(smtExprs);
      SmtExpr exists = SmtQtExpr.Op.EXISTS.make(and, existsSet.getVariables());
      return SmtQtExpr.Op.EXISTS.make(exists, smtVariables);
    }
    else
    {
      SmtExpr exists = SmtQtExpr.Op.EXISTS.make(and, smtVariables);
      return exists;
    }
  }

  private SmtExpr getMemberOrSubsetExpressions(List<SmtVariable> smtVariables)
  {
    SmtExpr andExpr = BoolConstant.True;
    for (SmtVariable smtVariable : smtVariables)
    {
      if (smtVariable.getConstraint() == null)
      {
        continue;
      }
      andExpr = SmtMultiArityExpr.Op.AND.make(andExpr, smtVariable.getConstraint());
    }
    return andExpr;
  }

  private SmtExpr translateOneQuantifier(SmtExpr body, List<SmtVariable> smtVariables,
                                         Environment environment, SmtExpr constraints)
  {
    // one x: e1, y: e2, ... | f(x, y, ...) is translated into
    // exists x, y, ... ( x in e1 and y in e2 and ... and constraints(x, y, ...) and f(x, y, ...) and
    //    for all x', y', ... (x in e1 and y in e2 ... and constraints(x', y', ...)
    //      and not (x' = x and y' = y ...) implies not f(x', y', ...)))

    SmtExpr multiplicity = getMemberOrSubsetExpressions(smtVariables);
    SmtExpr existsAnd = SmtMultiArityExpr.Op.AND.make(multiplicity, constraints, body);

    // create new variables x', y', ...
    List<SmtVariable> newVariables = TranslatorUtils.copySmtVariables(smtVariables);

    // build the expr (x' = x and y' = y ...)
    SmtExpr oldEqualNew = BoolConstant.True;
    for (int i = 0; i < smtVariables.size(); i++)
    {
      SmtVariable oldVariable = smtVariables.get(i);
      SmtVariable newVariable = newVariables.get(i);
      oldEqualNew = SmtMultiArityExpr.Op.AND.make(oldEqualNew, SmtBinaryExpr.Op.EQ.make(oldVariable.getVariable(), newVariable.getVariable()));
    }
    SmtExpr notOldEqualNew = SmtUnaryExpr.Op.NOT.make(oldEqualNew);

    // build a new body from the old one by replacing old variables with new variables
    SmtExpr newBody = body;
    for (int i = 0; i < smtVariables.size(); i++)
    {
      newBody = newBody.substitute(smtVariables.get(i).getVariable(), newVariables.get(i).getVariable());
    }
    newBody = SmtUnaryExpr.Op.NOT.make(newBody);

    SmtExpr newMultiplicity = getMemberOrSubsetExpressions(newVariables);

    SmtExpr forAllAnd = SmtMultiArityExpr.Op.AND.make(newMultiplicity, constraints, notOldEqualNew);

    SmtExpr implies = SmtBinaryExpr.Op.IMPLIES.make(forAllAnd, newBody);
    SmtExpr forAll = SmtQtExpr.Op.FORALL.make(implies, newVariables);
    existsAnd = SmtMultiArityExpr.Op.AND.make(existsAnd, forAll);
    SmtExpr exists = SmtQtExpr.Op.EXISTS.make(existsAnd, smtVariables);
    return exists;
  }

  private SmtExpr translateLoneQuantifier(SmtExpr body, List<SmtVariable> smtVariables,
                                          Environment environment, SmtExpr constraints)
  {
    // lone ... | f is translated into
    // (all ... | not f)  or (one ... | f)

    SmtExpr notBody = SmtUnaryExpr.Op.NOT.make(body);
    SmtExpr allNot = translateAllQuantifier(notBody, smtVariables, environment, constraints);
    SmtExpr one = translateOneQuantifier(body, smtVariables, environment, constraints);
    SmtExpr or = SmtMultiArityExpr.Op.OR.make(allNot, one);
    return or;
  }
}
