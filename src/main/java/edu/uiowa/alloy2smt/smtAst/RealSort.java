/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

public class RealSort extends Sort
{
    private final String realSort = "real";
    
    @Override
    public String toString() 
    {
        return this.realSort;
    }    
}
