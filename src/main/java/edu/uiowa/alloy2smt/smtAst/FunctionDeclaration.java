/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class FunctionDeclaration
{
    public List<Sort>   inputSort;
    public Sort         outputSort;
    
    public FunctionDeclaration(List<Sort> inputSort, Sort outputSort) 
    {
        this.inputSort  = inputSort;
        this.outputSort = outputSort;
    }
    
    public FunctionDeclaration(Sort inputSort, Sort outputSort) 
    {
        this.inputSort  = Arrays.asList(inputSort);
        this.outputSort = outputSort;
    }

    public FunctionDeclaration(Sort outputSort) 
    {
        this.inputSort  = new ArrayList<>();
        this.outputSort = outputSort;
    }    
}
