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

/**
Testing framework for X10 computation trees.

A test is provided as a fact for the reduceTest/2 (anoymous test) 
or reduceTest/3 (named test) predicate. The first (second) argument 
of reduceTest/2 (reduceTest/3) is a term representing an X10 statement, 
and the second (third) is an assertion that we  desire to test.
An assertion is of the form all(t) or some(t), where t is (for now)
a conjunction of assertions about values in the heap. The all(t)
test checks that all executions of the program result in a heap
taht satisfies t, the some(t) test checks that there is an execution
that satisfies t. 

TODO: provide support for full CTL.
e.g

reduceTest(       local x;x[0]=1,                  all(x[0]=1)).
reduceTest(test1, skip,                             all(true)).
reduceTest(test3, local x;x[0]=1;x[1]=1,          some(x[0]=1 & x[1]=1)).
reduceTest(test4, local x;async x[0]=0;x[1]=1,    all(x[1]=1 & x[0]=0)).
reduceTest(test5, local x;x[0]=0;async x[1]=1,    all(x[1]=1 & x[0]=0)).

@author vj

Sun Jul 20 15:48:39 EDT 2014
 vj added
    -- support for specifying tests with sub-statements rather than with paths.
       The user simply needs to make sure that the sub-statements PS singled out
       are such that there is a unique P s.t. path(S, P, PS) is true. 

       e.g. the user must now write:

hbTest(one, local x; clocked finish ( clocked async (x[1]=1; advance); advance; async x[2]=2), 
                x[1]=1, x[2]=2, true).

and not

hbTest(one, local x; clocked finish ( clocked async (x[1]=1; advance); advance; async x[2]=2), 
                1:cf:0:ca:0:nil, 1:cf:1:1:a:nil, true).

That is, the rule they must follow is that the substatements 
of interest to them (e.g. x[1]=1 and x[2]=2) occur uniquely
in S.
       
*/
:- use_module(x10).

testAll(Verbose) :- 
   myReduceTest(Name, X, As),
   test(Verbose, Name, X, As).
testAll(_).

myReduceTest(Name,  X, As) :- reduceTest(Name, X, As).
myReduceTest(_Name, X, As) :- reduceTest(X, As). % the name is an anon var

/**
  For the statements S in hbTests, test that if there are two paths P and Q such
  that hb(S, P, Q) is true, then there is no execution in which the label Q precedes
  the label P.
*/
hbProblems :-
  write('Searching for a problem in hb'), nl,
  myHBTest(_Name, S, _, _, _), % reuse hbTest's for hbProblems
  hbProblem(S, P, Q), 
  write(hbProblem(S, P, Q)).

hbProblems :-
  write('Searching for a problem with not hb:'),nl,
  myHBTest(_Name, S, _, _, _), % reuse hbTest's for hbProblems
  notHBProblem(S, P, Q), 
  write(notHBProblem(S, P, Q)).

hbProblems.

hbTestAll(Verbose) :-
  myHBTest(Name, S, PS, QS, Result),
  path(S, P, PS), path(S, Q, QS),  
  hbt(Verbose, Name, S, P, Q, Result).
hbTestAll(_).

myHBTest(Name,  S, PS, QS, Result) :- hbTest(Name, S, PS, QS, Result).
myHBTest(_Name, S, PS, QS, Result) :- hbTest(S, PS, QS, Result). % the name is an anon var


hbt(Verbose, Name, S, P, Q, false) :- 
  \+ hb(S, P, Q), !,
    path(S, P, PS), path(S, Q, QS), 
    (Verbose=verbose, write('(ok) '), write(Name), write(': '), 
     write(S), write(' |/- '), write(PS), write(' hb '), write(QS);
     (Verbose=silent, write(ok(Name)))).
hbt(verbose, Name, S, P, Q, false) :- 
    path(S, P, PS), path(S, Q, QS), 
    write('(fail) '), write(Name), write(': '), 
    write(S), write('|/- '), write(PS), write(' hb '), write(QS).
hbt(silent, Name, _S, _P, _Q, false) :- write(fail(Name)).

hbt(Verbose, Name, S, P, Q, true) :- 
  hb(S, P, Q), !,
    path(S, P, PS), path(S, Q, QS), 
    (Verbose=verbose, write('(ok) '), write(Name), write(': '), 
     write(S), write(' |- '), write(PS), write(' hb '), write(QS);
     (Verbose=silent, write(ok(Name)))).
hbt(verbose, Name, S, P, Q, true) :- 
    path(S, P, PS), path(S, Q, QS), 
    write('(fail) '), write(Name), write(': '), 
    write(S), write('|- '), write(PS), write(' hb '), write(QS).
hbt(silent, Name, _S, _P, _Q, true) :- write(fail(Name)).

  
/**
  Check that there is some execution of agent X
  that satisfies As.
*/
test(Verbose, Name, X, some(As)) :-
    X ==> label(Y, _Ps),
    check(As, Y, true), % failure wil cause backtracking
    !, 
    announceResult(Verbose, Name, X, some(As)).
/**
  Check that every execution of agent X satisfies As.
*/
test(Verbose, Name, X, all(As)) :-
    bagof(Y, X==>label(Y, _Ps), T), % collect all executions in T.
    checkAll(T, As, true), 
    !, 
    announceResult(Verbose, Name, X, all(As)).

test(verbose, N, X,  As) :- write(N), write(': '), write(test(X)), write(' |/- '), write(As).
test(silent,  N, _X, _As) :- write(N), write(' failed.').

announceResult(verbose, _N, X, As) :- write(test(X)), write(' |- '), write(As).
announceResult(silent,  N, _X, _As) :- write(ok(N)).

/*
announceResult(verbose, X, T, As) :- checkAll(T, As, true), ! , write(test(X)), write(' ok').
announceResult(verbose, X, T, As) :- checkAll(T, As, bad(H)), 
    write(test(X)), write(assert As), write(' failed for '), write(H).

announceResult(silent, _X,  T, As) :- assert(T, As, true), !.
announceResult(silent,  X, _T, _As) :- write(test(X)), write(' failed').
*/
checkAll([], _As, true).
checkAll([H | Hs], As, Result) :- check(As, H, R1), !, checkAll(Hs, As, R2), and(R1,R2,Result).
checkAll([H | _Hs], _As, bad(H)).

/** The (ground) lists S and T have the same multi-set of elements.*/
same(S, T):- sublist(S,T), sublist(T,S).
sublist([],_T).
sublist([A|R], T):- append(X,[A|Y], T), !, append(X,Y, XY), sublist(R, XY).

sameSets(S,T) :- subset(S,T), subset(T,S).
subset([],_T).
subset([A|X],T):- append(_,[A|_],T), !, subset(X,T).
