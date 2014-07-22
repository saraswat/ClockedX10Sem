Mon Jul 21 23:46:43 EDT 2014

This project contains the Prolog source code for the structural
operational semantics of (simplified) clocked X10 programs, being
developed by Tomofumi Yuki, Paul Feautrier, Sanjay Rajopadhye and
Vijay Saraswat.

The semantics handles basic statements (skip, assignment to array
variables, reads), async, finish, clocked async, clocked finish, and
structured for loops.

The main purpose of the semantics is to define a "happens before"
relation on statements. This can then be used to give a precise
statement-instance, element-instance static analysis for programs in
the polyhedral fragment of this simplified language.

This project builds on the semantics for X10 programs that appears in
PPoPP'13, and subsequent work to handle clock semantics, currently
under preparation for a journal submission.

The main technical result is a static characterization of the happens
before relation on basic sub-statements P and Q of a statement S. P hb Q
should be the case precisely when in all execution sequences for S the
step labeled with P occurs before the step labeled with Q.

The characterization for hb for clock-free programs is very simple and
given in PPoPP'13. This project contains the characterization for
arbitrary clocked programs.

People looking to  understand this code should start with
smallx10.pl. It is an extract of x10.pl that provides only the core 
reduction predicates.
