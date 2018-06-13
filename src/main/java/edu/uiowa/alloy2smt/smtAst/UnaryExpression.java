/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

public class UnaryExpression extends Expression
{
    public enum Op 
    {	        
        NOT ("not"),
        COMPLEMENT ("complement"),
        TRANSPOSE ("transpose"),
        TCLOSURE("-"),
        SINGLETON("singleton"),
        UNIVSET("as univset"),
        EMPTYSET("as emptyset");

        private final String opStr;

        private Op(String str) 
        {
            this.opStr = str;
        }

        @Override
        public String toString() 
        {
            return this.opStr;
        }    
    }     
}
