/*
 *  This file is part of the X10 project (http://x10-lang.org).
 *
 *  This file is licensed to You under the Eclipse Public License (EPL);
 *  You may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *      http://www.opensource.org/licenses/eclipse-1.0.php
 *
 *  (C) Copyright IBM Corporation 2014.
 * Based on initial code from Paul Feautrier.
 */
/*

Mon Jul 21 23:12:40 EDT 2014
  -- Moved to Git repository ClockedX10Sem

Mon Jul 21 17:08:31 EDT 2014
  -- Introduced phase distinction between in-phase basic actions and the advance that terminates a phase.

Mon Jul 21 12:29:13 EDT 2014
  -- Added fix for problem pointed out by Tomofumi. 

     I do not understand why you use last_cf for Q as the F. In
     general, you need to look at the common cf as the F. I believe
     that the nesting of clocked finishes can be captured by counting
     the phases up to the inner clocked finish, since the inner
     clocked finish is guaranteed to happen within the current phase
     of the outer clocked finish. This is described in Section 6.3.  

     Here is an example:
   16 ?- hb(local x; clocked finish (clocked async(clocked finish x[0] = 0); (advance; clocked async (clocked finish (x[1] = 1)))), 1:cf:0:ca:cf:nil, 1:cf:1:1:ca:cf:nil).
   false.

   However, one problem remains, as revealed by hbProblems:

Problem!notHBProblem(local x;clocked finish (clocked async clocked finish (advance;clocked async x[0]=0;clocked finish x[1]=1);advance;clocked async clocked finish x[2]=2),1:cf:0:ca:cf:0:nil,1:cf:1:0:nil)

Sun Jul 20 23:48:57 EDT 2014
  -- Added more support for hbProblems. Now this predicate will print out
     if it finds any violation (among the given programs) to the assertion:
      hb(S, P, Q) <-> forall ES for S. P precedes Q in ES

Sun Jul 20 13:55:44 EDT 2014
  -- Upgraded hb(S, P, Q) to work for all pairs of paths (P, Q).
     In particular, use the counting procedure for phases only if
     Q is in a cf, and P is also in the controlling cf F for Q, but
     P is now allowed to arbitrary (i.e. have its own cf's, f's, a's
     and ca's) that are not controlled by F. This is handled by 
     extending cft to return the prefix before the terminating f or cf
     (if any), and using that prefix to compute the phase of P. 

Sat Jul 19 10:14:00 EDT 2014
  -- Major reworking of phi, to fix two bugs.
     Bug 1: When checking phases, need to make sure both statements 
       are clocked by same finish.
     Bug 2: Need to make sure that the first statement not just starts
       before the second, but actually finishes before the second (it 
       could be in an unclocked async that spans phases).
     The fix is to introduce the concept of startPhase and endPhase.
     Analysis is below, with the definition of these predicates.
  -- Added hbTests as well. Please add as many tests as you can,
     both positive and negative!

Fri Jul 18 07:03:30 EDT 2014
  -- Added comments

Fri Jul 18 06:24:49 EDT 2014
vj added
  -- path predicate
  -- added annStmt
  -- ensured that substitute, ==>, => etc work with annotated
     stmts. Need to annotate statements, rather than build up
     paths during the proof of a transition because we need
     paths relative to the original root.
  -- fixed bug in definition of phi ... remember that bagof 
     fails instead of returning empty list
  -- added hbProblem/3 
Mon Jul 14 09:53:21 EDT 2014
vj added
  -- fix for yield bug -- ensure now that clock advance transition
     is made only when hasYield returns a different statement, that
     is, some advance is converted to a skip.
  -- fixed source syntax to use X10/C/Java syntax for assignment (l=r) rather
     than Pascal (l:=r).
  -- added some tests and all tests.
  -- converted all tests to new syntax, verified they pass.

Sun Jul 13 08:13:34 EDT 2014
vj added 
  -- support for a module.
  -- added a proper store, now it is a mapping from variables to values
     (instead of being a time-ordered list of updates to the store).
     array variables are supported. 
  -- added support for arithmetic expressions, other kinds of expressions can be 
     added in the obvious way.

vj added local statements to declare variables before use.
vj TODO: Check this works with Gnu Prolog.
   To use this file:
  - download the Gnu Prolog compiler:
      sudo apt-get install gprolog
    - compile the X10.pl file:
      gplc X10.pl
    - the result is an executable file, X10, which you can run with
      ./X10
    - at the prompt, either load the exemple file
      consult('examples.pl').
      and run examples simply by typing their "name", eg:
          ex_unclocked_3.
        Don't forget the final dot. If the example has parallelism,
        traces will be constructed one at time; to proceed to the next
        trace, type a semicolon (;) until you get a no!

      or you can build your own examples and submit them at the prompt.
*/
:-module(x10, [
% 1000 xfy ,
	     op(998, xfy, ';'),  % tighter than a ,; represents sequential comp
	     op(997, xfy, '=>'),  % one step reduction operator
	     op(997, xfy, '==>'), % big step, execute to termination operator
	     op(995, fy, clocked), % tighter than ;
	     op(995, fy, finish),
	     op(995, fy, async),
	     op(994, fy, local), % introduces a new local variable
	     op(994, fy, assert), 
% 990 xfx :=
             op(750, yfx, '&'),  
             op(700, xfx, '<<'),  % lexicographic order
             op(700, xfx, hb0),  
             op(300, xfy, '@'),  % annotations
             op(100, yf, []),
	     '=>'/2,
	     '==>'/2,
	     isSync/1,
	     isAsync/1,
             expr/2,
	     stmt/1,
             path/3,
             hasSubstatement/2,
             hasPath/2,
	     isClockedStuck/1,
	     hasYield/2,
	     check/3, 
	     and/3,
	     or/3, 
	     hb/3,
	     hbProblem/3, notHBProblem/3
	]).
:-use_module(library(assoc)).
:-use_module(corex10).

/**
  expr(+A) :- A is a legal expression in formal X10.
*/
expr(A, L)   :- app(_, A:_, L).
expr(A, _)   :- number(A).
%expr(A+B) :- expr(A), expr(B).
%expr(A*B) :- expr(A), expr(B).
%expr(A-B) :- expr(A), expr(B).
%expr(A/B) :- expr(A), expr(B).

/**
 stmt(+S) :- S is a top level statement in formal X10.

 The top level scope implicitly provides a finish, not a clocked finish.
*/
stmt(S) :- unclockedStmt(S, nil, _).

/** 
  clockedStmt(+Stmt) :- 
   A clocked stmt is one which executes in a scope in which an ambient
   clock has been established by a clocked finish.
   This predicate succeeds only when all substatements executed
   within a finish or an async are known to be unclocked.
*/

clockedStmt(advance, In, In).
clockedStmt(clocked async S, In, In) :- clockedStmt(S, In, _).

clockedStmt(skip,             In,   In).
clockedStmt(local E,          In, E:In) :- atom(E).
clockedStmt(L[I]=R,           In,   In) :- expr(L, In), expr(I, In), expr(R, In).
clockedStmt(for(X, L, U,S),   In,   In) :- atom(X), expr(L, In), expr(U, In), clockedStmt(S, X:In, _).
clockedStmt(async S,          In,   In) :- unclockedStmt(S, In, _).
clockedStmt(finish S,         In,   In) :- unclockedStmt(S, In, _).
clockedStmt(clocked finish S, In,   In) :- clockedStmt(S, In, _).
clockedStmt((S;T),            In,  In2) :- clockedStmt(S, In, In1), clockedStmt(T, In1, In2).


/** 
   unclockedStmt(+S) :- 
   Unclocked stmts execute in a scope in which 
   there is no ambient clock. Hence they cannot have a clocked
   async or an advance. However, they may start a new nested
   scope with its own ambient clock, i.e. they may start a 
   clocked finish.
*/
unclockedStmt(skip,             In,   In).
unclockedStmt(local E,          In, E:In) :- atom(E).
unclockedStmt(L[I]=R,           In,   In) :- expr(L, In), expr(I, In), expr(R, In).
unclockedStmt(for(X, L, U, S),  In,   In) :- atom(X), expr(L, In), expr(U, In), unclockedStmt(S, X:In, _).
unclockedStmt(async  S,         In,   In) :- unclockedStmt(S, In, _).
unclockedStmt(finish S,         In,   In) :- unclockedStmt(S, In, _).
unclockedStmt(clocked finish S, In,   In) :- clockedStmt(S, In, _). 
unclockedStmt((S; T),           In,  In2) :- unclockedStmt(S,In, In1), unclockedStmt(T, In1, In2).

basicStmt(skip).
basicStmt(advance).
basicStmt(local _).
basicStmt([_]=_).

/** 
  hasPath(+S, ?P) :- 
    P is a path in S. 
  On backtracking, enumerates all paths in S.
*/
hasPath(S, P) :- path(S, P, _).

/**
  hasSubstatement(+S, ?T):- 
    T is a substatement of S, i.e.
    there is a path P in S s.t. S(P)=T.
*/
hasSubstatement(S, T):- path(S, _, T).

/** hbProblem(+S, +P, +Q) :-
  S is a statement, P and Q are paths in it,
  hb(S, P, Q) is true, however there is an execution
  sequence Ps in which Q precedes P. So it tests violations
  of hb(S, P, Q) => \+ existsES(S, Q, P) by 
  checking hb(S,P,Q) and \+\+ existsES(S, Q, P).
*/
hbProblem(S, P, Q) :-
  path(S, P, S0), basicStmt(S0), path(S, Q, S1), basicStmt(S1),
  hb(S, P, Q), 
  print('Finding an ES for '), print(S) , print(' violating '), 
  print(stm(S0, P)), print(' precedes '), print(stm(S1,Q)), nl,  
  existsES(S, Q, P),
  print('Problem!').

/** Looks for violations of allES(S, P, Q) => hb(S, P, Q)
  by checking allES(S,P,Q) and \+ hb(S, P, Q).
*/
notHBProblem(S, P, Q) :-
  path(S, P, S0), basicStmt(S0), path(S, Q, S1), P \== Q, basicStmt(S1),
  print('Do all ES for '), print(S) , print(' satisfy '), 
  print(stm(S0, P)), print(' precedes '), print(stm(S1,Q)), nl,  
  allES(S, P, Q), 
  \+ hb(S, P, Q),
  print('Problem!').

allES(S, P, Q) :-
  bagof(Ps, X^(S ==> label(X, Ps)), Pss), 
  allPrecedes(Pss, P, Q).

allPrecedes([], _, _).
allPrecedes([Ps | Pss], P, Q):- precedes(P, Q, Ps), allPrecedes(Pss, P, Q).

existsES(S, P, Q) :-
  S ==> label(_, Ps),
  precedes(P, Q, Ps).

precedes(P, Q, P:R) :- app(_, Q:_, R).
precedes(P, Q, _:R) :- precedes(P, Q, R).

%%%%%%%%%%%% End of The HB Relations %%%%%%%%%%

/** check(Assertion, Heap, Result) :- 
  Check the heap satisfies the given assertion. Should be simplified.
*/ 
check(true,   _H, true).
check(X[V]=R,  H, Result):- eval(X[V], H, XVV), eval(R, H, RH), equals(XVV, RH, Result).
check((A & B), H, Result):- check(A, H, R1), check(B,H, R2), and(R1, R2, Result).
check((A | B), H, Result):- check(A, H, R1), check(B, H, R2), or(R1, R2, Result).

and(true, true, true).
and(true, false, false).
and(false, true, false).
and(false, false, false).

or(true, true, true).
or(true, false, true).
or(false, true, true).
or(false, false, false).

equals(X, Y, true) :- X==Y.
equals(X, Y, false):- X\==Y.

/**
Show: for all S, H. clockedStmt(S),  c(S,H)=> c(SS,HH) implies clockedStmt(SS).
Show: for all S, H. clockedStmt(S),  isClockedStuck(S), c(S,H)=> c(SS,HH) implies isClockedStuck(SS).
*/
