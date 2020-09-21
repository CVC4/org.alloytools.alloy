/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.parser.CompModule;
import edu.uiowa.smt.SmtEnv;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.List;

public class FuncTranslator
{
  private final Alloy2SmtTranslator translator;

  public FuncTranslator(Alloy2SmtTranslator translator)
  {
    this.translator = translator;
  }

  void translateFunctions()
  {
    for (CompModule module : translator.alloyModel.getAllReachableModules())
    {
      if (module.getModelName().contains("util/ordering") ||
          module.getModelName().contains("util/integer"))
      {
        continue;
      }
      for (Func func : module.getAllFunc())
      {
        if(func.label.startsWith("run$"))
        {
          // ignore command functions
          continue;
        }
        getFuncTranslation(func);
      }
    }
  }

  FunctionDeclaration getFuncTranslation(Func func)
  {
    FunctionDeclaration function;
    if(translator.functionsMap.containsKey(func.label))
    {
      function = translator.functionsMap.get(func.label);
    }
    else
    {
      function = translateFunc(func);
    }
    return function;
  }

  private FunctionDefinition translateFunc(Func func)
  {
    SmtEnv smtEnv = new SmtEnv();
    List<SmtVariable> arguments = new ArrayList<>();
    for (Decl decl : func.decls)
    {
      List<SmtVariable> variables = translator.exprTranslator.declTranslator.translateDecl(decl, smtEnv);
      // List<SmtVariable> setVariables = convertToSetVariables(variables);
      arguments.addAll(variables);
    }
    // add arguments to function environment
    for (SmtVariable variable : arguments)
    {
      smtEnv.put(variable.getName(), variable.getVariable());
    }

    SmtExpr smtExpr = translator.exprTranslator.translateExpr(func.getBody(), smtEnv);

    // if the return type has multiplicity one
    if(!func.isPred &&
        func.returnDecl instanceof ExprUnary &&
        ((ExprUnary) func.returnDecl).op == ExprUnary.Op.ONEOF &&
        smtExpr.getSort() instanceof SetSort
    )
    {
      // use the choose expr
      smtExpr = smtExpr.choose();
    }

    FunctionDefinition function = new FunctionDefinition(func.label, arguments, smtExpr.getSort(), smtExpr, true);

    translator.addFunction(function);

    return function;
  }

  private List<SmtVariable> convertToSetVariables(List<SmtVariable> variables)
  {
    List<SmtVariable> setVariables = new ArrayList<>();

    for (SmtVariable variable : variables)
    {
      if (variable.getSort() instanceof TupleSort)
      {
        Sort sort = new SetSort(variable.getSort());
        SmtVariable newVariable = new SmtVariable(variable.getName(), sort, variable.isOriginal());
        setVariables.add(newVariable);
      }
      else
      {
        setVariables.add(variable);
      }
    }
    return setVariables;
  }
}
