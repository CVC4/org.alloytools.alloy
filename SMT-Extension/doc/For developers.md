# Translation from Alloy to CVC4

The SMT-Extension translates alloyModels into CVC4 SMT-LIB.
The main class is Alloy2SmtTrnaslator which translates an alloy model (including modules, signatures, predicates, functions, and facts). 
Alloy commands are translated separately depending on whether a single command or all commands are executed. 
If multiple alloy commands are executed, each command is executed in a separate stack using smt commands push and pop. 

Here are the main classes used in the translation
```
+------------+                       +-----------+               +-----------+                       +---------------+
| AlloyModel |--Alloy2SmtTranslator->| SmtScript |--SMTRewriter->| SmtScript |--SMTLibPrettyPrinter->| SmtLib string |
+------------+                       +-----------+               +-----------+                       +---------------+
                                                                                                            |
                                                                                                        Cvc4Process
                                                                                                            V       
                                                                         +---------------+           +-------------+
                                                                         | CommandResult |<-parsing--| cvc4 string |
                                                                         +---------------+           +-------------+
```

# optimization ideas:

## Avoiding passing set arguments for predicates and functions

Alloy treats individual arguments as singletons and therefore alloy functions and predicates expect set arguments. 
Translating these functions directly into SMT functions without avoiding these set arguments is very bad and CVC4 may 
return `unknown` answer.
Although the syntax of function arguments determine the multiplicity of each argument, the semantics does not allow us to utilize this information and in fact alloy analyzer ignores these multiplicities.  

Several approaches have been attempted to avoid set arguments:

1. Treating alloy functions as macros and expanding function calls with the passed arguments. 
 This approach uses set arguments when they are needed and in most cases uses individual arguments. 
 However, the generated SMT is hard to read and optimize.
 
2. Translating alloy functions into SMT functions with set arguments, and relaying on the SMTRewriter to convert singleton arguments into individual arguments. 
This is the current implementation which is more readable than the previous one.
 However, converting singleton arguments into individual arguments is difficult at the level of SMT because in  many auxiliary generated sets in are passed as arguments.
 The performance of this approach so far is worse than the previous one, but I think it is the right approach and it would be fast if all singleton arguments are converted into individual arguments and unnecessary quantifiers are removed. 
 Another idea that I want to try is to implement a predicate `isSingleton` for each alloy expression. 
 If this is possible, then based on the usage of alloy functions, we can convert singleton arguments into individual arguments.
 

## Using Smt (let, tupSel and choose operators) instead of existential quantifiers

Using choose operators and tupSel is faster than using existential quantifiers especially for alloy assertions
which convert these existential quantifiers into universal quantifiers. 
The question is, why did I use existential quantifiers in the first place?
This is because CVC4 did not support `choose` operator for singletons and existential variables are generated  
to define the semantics of arithmetic operators.
If `isSingleton` predicate is implemented for alloy expressions, then `choose` operator is ideal and replaces these
existential variables. 

However, this does not remove the need for existential quantifiers for non-singleton sets.
Example: 
```
fact {plus[A, B] = X.Y}
```
Initially I defined `(declare-fun plus ((A (Set (Tuple UInt))) (B (Set (Tuple UInt)))) (Set (Tuple UInt)))`
and added assertions for the addition operation. However, this function is too general, and I only need the result 
of `plus[A, B]`. 
So I modified the code to generate an existential quantifier `exists C = { z \| ∃ x ∈ A, y ∈ B. x + y = z }`.


For comparison we may need to change the semantics so that for non-singular sets, the output is nondeterministic. 
For example `{2} > {1, 3}` is `false` in our written semantics, but with `choose` operator, `{2} > {1, 3}` is true
if `1` is chosen, and false if `3` is chosen. 