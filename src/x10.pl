/*
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
:-module(x10vj, [
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
             expr/1,
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

/**
  expr(+A) :- A is a legal expression in formal X10.
*/
expr(A)   :- atomic(A).
expr(A+B) :- expr(A), expr(B).
expr(A*B) :- expr(A), expr(B).
expr(A-B) :- expr(A), expr(B).
expr(A/B) :- expr(A), expr(B).

/**
 stmt(+S) :- S is a top level statement in formal X10.

 The top level scope implicitly provides a finish, not a clocked finish.
*/
stmt(S) :- unclockedStmt(S).

/** 
  clockedStmt(+Stmt) :- 
   A clocked stmt is one which executes in a scope in which an ambient
   clock has been established by a clocked finish.
   This predicate succeeds only when all substatements executed
   within a finish or an async are known to be unclocked.
*/

clockedStmt(advance).
clockedStmt(clocked async S) :- clockedStmt(S).

clockedStmt(skip).
clockedStmt(local E)         :- atom(E).
clockedStmt(L[I]=R)          :- expr(L), expr(I), expr(R).
clockedStmt((S;T))           :- clockedStmt(S), clockedStmt(T).
clockedStmt(for(X, L, U,S))  :- atom(X), expr(L), expr(U), clockedStmt(S).
clockedStmt(async S)         :- unclockedStmt(S).
clockedStmt(finish S)        :- unclockedStmt(S).
clockedStmt(clocked finish S):- clockedStmt(S).


/** 
   unclockedStmt(+S) :- 
   Unclocked stmts execute in a scope in which 
   there is no ambient clock. Hence they cannot have a clocked
   async or an advance. However, they may start a new nested
   scope with its own ambient clock, i.e. they may start a 
   clocked finish.
*/
unclockedStmt(skip).
unclockedStmt(local E)          :- atom(E).
unclockedStmt(L[I]=R)           :- expr(L), expr(I), expr(R).
unclockedStmt((S; T))           :- unclockedStmt(S), unclockedStmt(T).
unclockedStmt(for(X, L, U, S))  :- atom(X), expr(L), expr(U), unclockedStmt(S).
unclockedStmt(async  S)         :- unclockedStmt(S).
unclockedStmt(finish S)         :- unclockedStmt(S).
unclockedStmt(clocked finish S) :- clockedStmt(S). 

basicStmt(skip).
basicStmt(advance).
basicStmt(local _).
basicStmt([_]=_).

/**
  annStmt(+S,?SS) :- SS is S with each substatement 
  annotated with the path from the root.
  Need to do this in the original statement, since 
  paths will change as the statement evolves.

  The term P@S represents sub-statement S annotated with path P
  from the root. 
*/
annStmt(S, SS) :- annStmt(S, nil, SS).

annStmt(advance,          P, P@advance).
annStmt(skip,             P, P@skip).
annStmt(local E,          P, P@(local E)).
annStmt(L[I]=R,           P, P@(L[I]=R)).
annStmt(clocked async S,  P, P@(clocked async SS)) :- app(P, ca:nil, PP), annStmt(S, PP, SS).
annStmt((S;T), P, P@(SS;TT)) :- 
   app(P, 0:nil, P0), annStmt(S, P0, SS), 
   app(P, 1:nil, P1), annStmt(T, P1, TT). 
annStmt(for(X, L, U, S),  P, P@for(X, L, U, SS))   :- app(P, X:nil,  PP), annStmt(S, PP, SS).
annStmt(async          S, P, P@(async SS))         :- app(P, a:nil,  PP), annStmt(S, PP, SS).
annStmt(finish         S, P, P@(finish SS))        :- app(P, f:nil,  PP), annStmt(S, PP, SS).
annStmt(clocked finish S, P, P@(clocked finish SS)):- app(P, cf:nil, PP), annStmt(S, PP, SS).

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

/** path(+S, ?P, ?T) :-
     T is the substatement of S reached by following
     path P from the root. On backtrackng enumerates
     all paths P (and the associated T).
*/
path(advance,           nil, advance).
path(skip,              nil, skip).
path(local E,           nil, local E).
path(L[I]=R,            nil, L[I]=R).
path((S;_),             0:P, U):- path(S, P, U).
path((_;S),             1:P, U):- path(S, P, U).
path(for(X, _L, _U, S), X:P, U):- path(S, P, U).
path(async S,           a:P, U):- path(S, P, U).
path(finish S,          f:P, U):- path(S, P, U).
path(clocked finish S, cf:P, U):- path(S, P, U).
path(clocked async  S, ca:P, U):- path(S, P, U).

%%%%%%%%%%%% The HB Relations %%%%%%%%%%

/** 
  +S << +T :- 
    S is lexicographically before T.
*/

0:_ << 1:_.
A:S << A:T :- S << T.

  /**
    cft(+S, ?T) :-
     S = T K U or T, where T is a sequence in {0,1,ca}*, K is
     cf or f, and U is any sequence.

    (The name is taken from the pattern c f t in the PPoPP paper
     where c stands for a seq in {0,1}*, f is the finish
     and t is any sequence. For clocked programs, clocked finish 
     is also a finish, so it has to be treated the same as f. ca's
     are also ok, i.e. the same as 0 or 1, because we use phase 
     counts to account for termination of substatements of ca's.)
    )

 */
  cft(S):- cft(S, _).

  cft(nil, nil).
  cft(f:_, nil).
  cft(cf:_, nil).
  cft(0:S, 0:T):- cft(S, T).
  cft(1:S, 1:T):- cft(S, T).
%  cft(ca:S, ca:T):- cft(S, T).

/** 
 The hb relation on paths from PPoPP '13 (for unclocked programs), 
 extended to handle clocked programs. hb for clocked programs
 uses hb0.
*/
0:S hb0 1:_ :- cft(S).
A:S hb0 A:T :- S hb0 T.

  not_cfs(nil).
  not_cfs(X:S) :- not_cf(X), not_cfs(S).
  not_cf(0).
  not_cf(1).
  not_cf(a).
  not_cf(f).
  not_cf(ca).

  ints(nil).
  ints(0:S):- ints(S).
  ints(1:S):- ints(S).

  app(nil, X, X).
  app(X:S, T, X:U):- app(S, T, U).

  ints_app(   S,    T, U) :- app(S, T, U), ints(T).
  last_cf(S, cf:T, U) :- app(S, cf:T, U), not_cfs(T).

  strict_before(0:nil, 1:_).
  strict_before(A:S, A:T):- strict_before(S,T).


  /** 
    R (= Alpha cf BO B1) is the path to an advance in S that is 
    within the same clocked finish scope as Alpha cf B
    (the target statement whose phase we are trying to 
    determine) and that will execute before Alpha cf B.
    For this we need B0 to be a strictly before prefix of B,
    and we need the remainder B1 to be just a sequence of 0's and 1's.
  */
  advanceBefore(S, Alpha, B, R):- 
    path(S, R, advance),    % gen all possible R's in S
    app(Alpha, cf:B0B1, R), % they must have an alpha prefix: TODO fold this into the gen
    strict_before(B0, B), 
    ints_app(B0, _, B0B1).


/** 
   phi(+S, +Alpha, +B, ?N) :- 
   the statement instance P = Alpha cf B of S is in controlled by 
   a cf at path Alpha, and P has phase N on the Alpha clock. 

   <p>S must be a loop free program (no for-loops permitted).
   P must be a legal path in it. N is computed to be the phase 
   in which S(P) starts.  

   <p>This measures  # advances of the Alpha clock executed by 
   activity A0 before it executes S(P) 
   + #advances of the Alpha clock executed by the clocked activity A1 
   that spawned A0 (before it spawned A0), 
   + #advances executed by the clocked activity A2 that 
     spawned A1 (before it spawned A1), ... all the way up to the 
   controlling clocked finish. 
*/

phi(S, Alpha, B, N) :- 
    (bagof(R, advanceBefore(S, Alpha, B, R), Rs); Rs=[]),
    length(Rs, N).


  alphaCFPrefix(nil, nil, nil).
  alphaCFPrefix(f:_, nil, nil).
  alphaCFPrefix(cf:_, nil, cf).
  alphaCFPrefix(a:_, nil, a).
  alphaCFPrefix(0:S, 0:T, Z):- alphaCFPrefix(S, T, Z).
  alphaCFPrefix(1:S, 1:T, Z):- alphaCFPrefix(S, T, Z).
  alphaCFPrefix(ca:S, ca:T, Z):- alphaCFPrefix(S, T, Z).

/**
hb(+S, +P, +Q):- 
  This predicate defines the static happens before relationship
  between substatement instances (at P and Q) of a statement S.
  S must be loop free.
*/
hb(S, P, Q) :- 
  common_cf(P, Q, Alpha, PreBP, PreBQ), 
  %last_cf(Alpha, cf:B, Q), 
  alphaCFPrefix(PreBQ, BQ, _), 
  phi(S, Alpha, BQ, N1), 
  path(S, Q, SQ), adjustPath(SQ, PreBQ, N1, N),
  %  app(Alpha, cf:PreB, P), 
  alphaCFPrefix(PreBP, BP, Z), Z \==a,
  phi(S, Alpha, BP, M1), 
  path(S, P, SP), adjustPath(SP, PreBP, M1, M),
  M < N.

hb(_, P, Q) :- P hb0 Q.

adjustPath(advance, Pre, M1, M):- not_cfs(Pre), M is M1+0.1.
adjustPath(advance, Pre, M, M):- \+(not_cfs(Pre)).
adjustPath(X, _Pre, M, M) :- X \== advance.

ok(0:A, 0:B) :- ok(A, B).
ok(1:A, 1:B) :- ok(A, B).
ok(ca:A, ca:B) :- ok(A, B).
ok(a:A, a:B) :- ok(A, B).
ok(f:A, f:B) :- ok(A, B).
ok(nil, _).
ok(_, nil).
ok(X:_, Y:_):- X \== Y.

common_cf(X, Y, Alpha, PreBX, PreBY) :- 
  app(Alpha, cf:PreBX, X), 
  app(Alpha, cf:PreBY, Y), 
  ok(PreBX, PreBY).



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

%%%%%%%%%%%% The dynamic semantics, ==> and => %%%%%%%%%%

/*
Substitution
 substitute(+Term, +Var, +Val, ?Term1) :- Term1 is obtained from Term by subtituting Val for Var.
*/

substitute(P@A, X, V, P@AA):- substitute(A, X, V, AA).
substitute(A,               _X, _V, A)  :- integer(A).
substitute(A,                A,  V, V)  :- atom(A).
substitute(A,                X, _V, A)  :- atom(A), A \== X.
substitute(local E,         _X, _V, local E).
substitute(async A,          X,  V, async AA)         :- substitute(A,X,V,AA).
substitute(finish A,         X,  V, finish AA)        :- substitute(A,X,V,AA).
substitute(clocked async A,  X,  V, clocked async AA) :- substitute(A,X,V,AA).
substitute(clocked finish A, X,  V, clocked finish AA):- substitute(A,X,V,AA).
substitute((A;B),            X,  V, (AA;BB))          :- substitute(A,X,V,AA), substitute(B,X,V,BB).
substitute(L[I]=R,           X,  V, L[II]=RR)         :- substitute(I,X,V,II), substitute(R,X,V,RR).
substitute([A|B],            X,  V, [AA|BB])          :- substitute(A,X,V,AA), substitute(B,X,V,BB).

/**
Lemma: For all S s.t. stmt(S) 
(a) isAsync(S) terminates
(b) isSync(S) terminates
(c) isAsync(S) xor isSync(S)

<p> Being isAsync means that if this statement S is in a composition S;T, 
then T can get started. Note in particular that for S;T to be 
async, both S and T have to be async. E.g. B=async(A);x=3 is not
async since in {B;C} B has to execute (the substatement x=3) before
C can be activated.
*/
isAsync(_@S):- isAsync(S).
isAsync(async _X).
isAsync((clocked async _S)).
isAsync((S;T))             :- isAsync(S), isAsync(T). 
isAsync(for(_X,_E1,_E2,S)) :- isAsync(S).

/**
The rules for isSync(S) follow from isAsync(S) and the desired properties of
isAsync(S) and isSync(S). 
*/
isSync(_@S):- isSync(S).
isSync(skip).
isSync(advance).
isSync(_L[_I]=_R).
isSync(local _S).
isSync(finish _S).
isSync(clocked finish _S).
isSync(for(_X,_E1,_E2,S)) :- isSync(S).
isSync(S;_T) :- isSync(S).
isSync(_T;S) :- isSync(S).

/* isClockedStuck(S, C) :- S is the body of a clocked finish statement that is 
   stuck, waiting for the clock to advance. C is true iff there is at least 
   one activity registered on the implicit clock, waiting to advance. Here it is 
   worth noting that isClockedStuck(clocked finish async S, true) should fail since
   the main activity (the body of clocked finish) has spawned an async S, reached the 
   end of the block in the body of the clocked finish, and deregistered itself 
   from the implicit clock. Hence, indeed, there is no activity registered on the
   clock.

   <p>Note that a clockedStuck statement cannot contain a nested
   clocked finish scope... all such scopes must terminate first 
   (hence, disappear).  Hence a clocked finish _S is not, recursively,
   stuck.

   <p> Similarly, if isClockedStuck(S), then S cannot contain a nested
   finish F that is not itself within an async child of S. (Otherwise 
   F is being executed by an activity registered on the clock, and must
   complete, i.e. disappear, before the clock can advance.)

  <p>Hence no clauses for
  isClockedStuck(skip, _) :-
  isClockedStuck(local E, _) :-
  isClockedStuck(_A[_B]=_C, _) :-
  isClockedStuck(for(...), _) :-
  isClockedStuck(clocked finish _S, _) :- 
  isClockedStuck(finish _S, _) :-

*/
isClockedStuck(S) :- hasYield(S, _, true).

/**
  hasYield(S,T) holds if S isClockedStuck, and the yield of S is T, 
  where the yield of S is defined by taking every clocked async substatement
  of S (that is not itself nested in a clocked finish substatement of S) --
  such a statement must have advance as its only activated statement, and taking
 the residual of such clocked asyncs, i.e. the statements in the sequential 
 continuation of the advance. 
*/
%hasYield(S, T):- clockedStmt(S), isClockedStuck(S, true), yield(S,T).


hasYield(S, T) :- hasYield(S, T, true).

hasYield(P@advance, P@skip, true).
hasYield(P@(clocked async S), P@(clocked async T), C) :- hasYield(S,T, C).
hasYield(P@(S;T), P@(SS; T), C) :- isSync(S), hasYield(S,SS, C).
hasYield(P@(S;T), P@(SS;TT), C) :- isAsync(S), hasYield(S,SS, C1), hasYield(T,TT, C2), or(C1, C2, C).
hasYield(P@(async S), P@(async S), false).


/* 
The big step rule.
*/
S ==> label(HH,Ps) :- annStmt(S, SS), store(H), reduce(c(SS, H), t(HH), Ps).

reduce(c(S, H), t(HH),  P:nil) :- c(S, H) => t(HH, P).
reduce(c(S, H), t(HHH), P:Ps)  :- c(S, H) => c(SS,HH, P), reduce(c(SS, HH), t(HHH), Ps).


c(P@skip,               H) => t( H, P).
c(P@(local X),          H) => t(HH, P)   :- empty_assoc(E), update(X, E, H, HH).
c(P@(L[I]=R),           H) => t(HH, P)   :- update(L[I]=R, H, HH).
c(_@(S;T),              H) => c(T, HH, P):- c(S,H) => t(HH, P).
c(_@(S;T),              H) => c(S, HH, P):- isAsync(S), c(T,H) => t(HH, P).
c(_@(async S),          H) => t(HH, P)   :- c(S, H) => t(HH, P).
c(_@(finish S),         H) => t(HH, P)   :- c(S, H) => t(HH, P).
c(P@(for(_X,E1,E2,_S)), H) => t(H,  P)   :- E1 > E2.
c(_@(clocked  async S), H) => t(HH, P)   :- c(S, H) => t(HH, P).
c(_@(clocked finish S), H) => t(HH, P)   :- c(S, H) => t(HH, P).

c(Q@(async S),          H) => c(Q@(async SS),          HH, P)   :- c(S, H) => c(SS, HH, P).
c(Q@(finish S),         H) => c(Q@(finish SS),         HH, P)   :- c(S, H) => c(SS, HH, P).
c(Q@(S;T),              H) => c(Q@(S; TT),             HH, P)   :- isAsync(S), c(T, H) => c(TT, HH, P).
c(Q@(S;T),              H) => c(Q@(SS; T),             HH, P)   :- c(S, H) => c(SS, HH, P).
c(Q@(clocked  async S), H) => c(Q@(clocked  async SS), HH, P)   :- c(S, H) => c(SS, HH, P).
c(Q@(clocked finish S), H) => c(Q@(clocked finish SS), HH, P)   :- c(S, H) => c(SS, HH, P).
c(Q@(clocked finish S), H) => c(Q@(clocked finish T),  H, Q)    :- hasYield(S,T).
c(Q@for(X, E1, E2, S),  H) => c((for(Q,E1)@SS; Q@for(X, EE, E2, S)), H, for(Q)):- % new labels
   E1 =< E2, EE is E1 + 1, substitute(S, X, E1, SS).


/** eval(+T, +Store, ?Val) :- 
 evaluate T, using the Store to look up values for variables,
 and return Val.
*/
eval(X, _Store,  X):- number(X); string(X).
eval(X,   Store, Y):- get_assoc(X, Store, Y). % Fails if no value associated
eval(X[I],Store, Y):- eval(X, Store, Xv), eval(I, Store, Iv), get_assoc(Iv, Xv, Y).
eval(A+B, Store, Y):- eval(A,Store,Av), eval(B, Store,Bv), Y is Av+Bv.
eval(A/B, Store, Y):- eval(A,Store,Av), eval(B, Store,Bv), Y is Av/Bv.
eval(A-B, Store, Y):- eval(A,Store,Av), eval(B, Store,Bv), Y is Av-Bv.
eval(A*B, Store, Y):- eval(A,Store,Av), eval(B, Store,Bv), Y is Av*Bv.

store(X):- empty_assoc(X).
update(L[I]=R, H, HH) :- eval(L, H, Lv), eval(I, H, Iv), eval(R, H, Rv), update(L, Lv, Iv, Rv, H, HH).
update(L, Lv, Iv, Rv, H, HH):- put_assoc(Iv, Lv, Rv, Xv1), put_assoc(L, H, Xv1, HH).
update(X, Val, H, HH) :- atom(X), put_assoc(X, H, Val, HH).

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
