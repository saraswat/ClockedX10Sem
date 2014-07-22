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

:- use_module(x10).
/* Examples */

reduceTest(skipTest, skip,                                  all(true)).
reduceTest(          local x;x[0]=1,                        all(x[0]=1)).
reduceTest(          local x;x[0]=1;x[1]=1,                 all(x[0]=1 & x[1]=1)).
reduceTest(          local x;async x[0]=0;x[1]=1,           all(x[1]=1 & x[0]=0)).
reduceTest(          local x;x[0]=0;async x[1]=1,           all(x[1]=1 & x[0]=0)).
reduceTest(          local x;finish (async x[0]=1; x[0]=0), all(x[0]=1 | x[0]=0)).
reduceTest(          local x;for(i,0,1,x[i]=i),             all(x[0]=0 & x[1]=1)).
reduceTest(          local x;finish for(i,0,1,async x[i]=i),all(x[0]=0 & x[1]=1)).

/* The same, up to termination. 
         Notice there are only 2 traces, but 8 answers! */
reduceTest(local a;local b; finish for(i,0,1,(a[i]=i;async b[i]=i)), all(a[0]=0 & a[1]=1 & b[0]=0&b[1]=1)).

reduceTest(local x; 
	   clocked finish (
		       clocked async (x[0]=0;advance);
		       advance;
		       x[0]=1), 
	   all(x[0]=1)).


/* In this example, advances serve to sequentialize two apparently parallel
   activities.

*/
reduceTest(local x; 
	   clocked finish (
		       clocked async (x[0]=0;advance);
		       advance;
		       x[0]=1), 
	   all(x[0]=1)).

reduceTest(local a; 
	   local b;
	   clocked finish 
		   for(i, 0, 1, 
			clocked async (
				    a[i]=i;
				    advance; 
				    b[i]=i
				)
		      ),
	   all(a[0]=0&a[1]=1&b[0]=0&b[1]=1)).

/*x10vj:store(X), bagof(Y, x10vj:reduce(c(local a; 
	   local b;
	   clocked finish 
		   for(i, 0, 1, 
			clocked async (
				    a[i]=i;
				    advance; 
				    b[i]=i
				)
		      ), X), t(Y)), Ys), length(Ys, L), write(length(L)), write(Ys),x10vj:checkAll(Ys, (a[0]=0&a[1]=1&b[0]=0&b[1]=1), Result).*/

reduceTest(local a; 
	   local b;
	   clocked finish 
		   for(i, 0, 1, 
			clocked async (
				    a[i]=i;
				    advance; 
				    b[i]=i
				)
		      ),
	   all(a[0]=0&a[1]=1&b[0]=0&b[1]=1)).


reduceTest(local a; 
	   clocked finish (
		       advance;
		       a[0]=1;
		       async a[0]=0
		   ), 
	   all(a[0]=0)).

reduceTest(local a; 
	   clocked finish (
		       advance;
		       a[1]=1;
		       async a[0]=0
		   ), 
	   all(a[0]=0&a[1]=1)).

%exy
reduceTest(local a; 
	   clocked finish (
		       clocked async a[0]=0;
                       advance
		   ), 
	   all(a[0]=0)).

%exz
reduceTest(local a; 
	   clocked finish (
		       clocked async a[0]=0;
                       advance
		   ), 
	   all(a[0]=0)).


reduceTest(local a; 
	   clocked finish (
		       clocked async (a[0]=0; advance);
                       a[1]=1
		   ), 
	   all(a[0]=0&a[1]=1)).

reduceTest(local a; 
	   clocked finish (
		       clocked async a[0]=0; 
		       advance;
                       async a[1]=1
		   ), 
	   all(a[0]=0&a[1]=1)).


reduceTest(local a; 
	   clocked finish (
		       clocked async (a[0]=0; advance);
                       async a[0]=1
		   ), 
	   all(a[0]=1 | a[0]=0)).

reduceTest(local a; 
	   clocked finish (
		       clocked async (a[0]=0; advance);
                       async a[0]=1
		   ), 
	   some(a[0]=1)).

reduceTest(local a; 
	   clocked finish (
		       clocked async (a[0]=0; advance);
                       async a[0]=1
		   ), 
	   some(a[0]=0)).

reduceTest(local a; 
	   clocked finish (
		       clocked async (a[0]=0; advance);
		       advance;
                       async a[0]=1
		   ), 
	   all(a[0]=1)).

% This test ensures that an activity registered on a clock executing a finish 
% completes that finish before advancing the clock.
reduceTest(local a; 
	   clocked finish (
	       clocked async (advance; a[0]=1);
	       finish async a[0]=0
	   ), 
	   all(a[0]=1)).



/* The canonical example */

yieldTest(local x; clocked async advance; advance;x[0]=1, clocked async skip; skip;x[0]=1).

hbTest('a seq before b => a hb b',
       local x; 
       x[1]=1;
       x[2]=2,
       x[1]=1, x[2]=2, true).

hbTest('async a seq before b => not (a hb b)',
       local x; 
       async x[1]=1;
       x[2]=2,
       x[1]=1, x[2]=2, false).

hbTest('async a seq 1 before b => not (a hb b)',
       local x; 
       x[0]=0;
       async x[1]=1;
       x[2]=2,
       x[1]=1, x[2]=2, false).

hbTest('async a seq 11 before b => not (a hb b)',
       local x; 
       x[0]=0;
       x[3]=3;
       async x[1]=1;
       x[2]=2,
       x[1]=1, x[2]=2, false).

hbTest('finish async a before b => (a hb b)',
       local x;
       finish
	   async x[1]=1;
       x[2]=2,
       x[1]=1, x[2]=2, true).

hbTest('finish async a seq 1 before b => (a hb b)',
       local x; 
       x[0]=0;
       finish async x[1]=1;
       x[2]=2,
       x[1]=1, x[2]=2, true).

hbTest('finish async a seq 11 before b => (a hb b)',
       local x; 
       x[0]=0;
       x[3]=3;
       finish async x[1]=1;
       x[2]=2,
       x[1]=1, x[2]=2, true).


hbTest('finish seq async a before b => (a hb b)',
       local x;
       finish (
	   async x[1]=1;
           x[0]=0
	   );
       x[2]=2,
       x[1]=1, x[2]=2, true).

hbTest('a in seq 0 before b => a hb b)',
       local x;
       x[1]=1;
       x[0]=0;
       x[2]=2,
       x[1]=1, x[2]=2, true).

hbTest('a in seq 1 before b => a hb b)',
       local x;
       x[0]=0;
       x[1]=1;
       x[2]=2,
       x[1]=1, x[2]=2, true).

hbTest('finish async a in seq 1 before b => (a hb b)',
       local x;
       finish (
           x[0]=0;
	   async x[1]=1
	   );
       x[2]=2,
       x[1]=1, x[2]=2, true).

hbTest('a in seq 1 before clocked b => (a hb b)',
       local x;
       x[1]=1;
       clocked finish x[2]=2,
       x[1]=1, x[2]=2, true).

hbTest('a in seq 1 before clocked finish async b => (a hb b)',
       local x;
       x[1]=1;
       clocked finish async x[2]=2,
       x[1]=1, x[2]=2, true).

hbTest('a in seq 1 before clocked finish seq 1 async  b => (a hb b)',
       local x;
       x[1]=1;
       clocked finish (
		   x[3]=3;
		   async x[2]=2
		   ),
       x[1]=1, x[2]=2, true).



hbTest(one, 
       local x; 
       clocked finish ( 
		   clocked async (
			       x[1]=1; 
			       advance); 
		   advance; 
		   async x[2]=2), 
                x[1]=1, x[2]=2, true).
hbTest(two,
       local x; 
       clocked finish (
		   async x[1]=1; 
		   advance; 
		   async x[2]=2), 
       x[1]=1, x[2]=2,false).

hbTest(three, 
       local x; 
       clocked finish (async x[1]=1; 
		       clocked finish x[0]=0;
		       advance; 
		       async x[2]=2), 
       x[0]=0, x[2]=2, true).

hbTest('P in its own async clocked finish', 
       local x; 
       async clocked finish (
		 advance; 
		 x[1]=1); 
       clocked finish( 
		   advance; 
		   advance; 
		   x[2]=2), 
       x[1]=1, x[2]=2, false).

hbTest(local x; 
       clocked finish (
		   advance; 
		   x[1]=1); 
       clocked finish( 
		   advance; 
		   advance; 
		   x[2]=2), 
       x[1]=1, x[2]=2, true).

hbTest(local x;
       clocked finish (
		   clocked async (x[1]=1;advance);
		   x[2]=2;
		   advance;
		   async x[3]=3), 
       x[1]=1, x[2]=2, false).

hbTest(local x; 
       clocked finish (
		   clocked async(
			       clocked finish x[1] = 1); 
		   (advance; 
		    clocked async (
				clocked finish (x[2] = 2)))), 
       x[1]=1, x[2]=2, true). 

hbTest(local x; 
       clocked finish (
		   clocked async(
			       clocked finish (
					   advance;
					   clocked async x[0] = 0;
					   clocked finish x[1]=1
				       ) 
			   );
		   advance; 
		   clocked async 
			   clocked finish x[2] = 2), 
       x[1]=1, x[2]=2, true). 

hbTest(local x; 
       clocked finish (
		   clocked async(
			       clocked finish (
					   advance;
					   clocked async x[0] = 0;
					   clocked finish x[1]=1
				       ) 
			   );
		   advance; 
		   clocked async 
			   clocked finish x[2] = 2), 
       x[0]=0, x[2]=2, true). 



