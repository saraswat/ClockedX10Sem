(* Semantics of Clocked X10 *)
(* (c) IBM 2014 *)

Require Import Notations.
Require Import Logic.
Require Import List.

Definition var := nat.

(* the type of abstract syntax nodes *)
Inductive asn : Type  :=
  | seq(n:nat) : asn
  | v(v:var) :asn
  | a :asn
  | f :asn.

Inductive expr : Type :=
  | val(i:nat):expr
  | vexp(v:var):expr.

Inductive heap : Type :=
  | null: heap
  | loc(l:var) (h:heap):heap
  | up(l:var) (i:expr) (e:expr) (h:heap):heap.

(* We choose to define stmt as a function from types
  so that we can annotate a statement with any kind of value.
  In reality, we are only interested in stmt unit and stmt (List asn). *)


Inductive stmt (A:Type):Type:=
  | Skip(a:A): stmt A
  | Local (e:var)(a:A): stmt A
  | Assign (l:var) (i:expr) (r:expr)(a:A): stmt A    (* L[I] = R *)
  | Xseq (c1:stmt A) (c2:stmt A)(a:A): stmt A
  | Xfor (x:var) (l:expr) (u:expr) (s:stmt A) (a:A): stmt A
  | Async (c:stmt A)(a:A): stmt A
  | Finish (c:stmt A)(a:A): stmt A.

Definition isBasic (A:Type)(s:stmt A):Prop := 
  match s with
    | Skip _ => True
    | Local _ _  => True
    | Assign _ _ _ _  => True
    |  _ => False
  end.

Definition ustmt := stmt unit.
Definition pth := list asn.
Definition ann_stmt := stmt pth.

Definition skip:ustmt := Skip unit tt.
Definition local (e:var):ustmt := Local unit e tt.
Definition assign (l:var)(i:expr) (r:expr):ustmt := Assign unit l i r tt.
Definition xseq (c1:ustmt)(c2:ustmt):ustmt := Xseq unit c1 c2 tt.
Definition xfor (x:var)(l:expr) (u:expr) (s:ustmt):ustmt := Xfor unit x l u s tt.
Definition async (c:ustmt):ustmt := Async unit c tt.
Definition finish (c:ustmt):ustmt := Finish unit c tt.


Inductive path A: stmt A -> pth -> stmt A -> Prop :=
 | path_skip: forall a, path A (Skip A a) nil (Skip A a)
 | path_local: forall a V, path A (Local A V a) nil (Local A V a)
 | path_assign: forall a L I R, path A  (Assign A L I R a) nil (Assign A L I R a)
 | path_seq0:  forall a S T P U, path A S P U -> path A (Xseq A S T a) ((seq 0) :: P) U
 | path_seq1:  forall a S T P U, path A S P U -> path A (Xseq A T S a) ((seq 1)::  P) U
 | path_x: forall a X L H U S P, path A S P U -> path A (Xfor A X L H S a) ((v X) :: P) U
 | path_a: forall aa S P U, path A S P U -> path A (Async A S aa) (a :: P) U
 | path_f: forall a S P U, path A S P U -> path A (Finish A S a)  (f ::P) U.

Definition hasBasicPath (s: ustmt)(p:pth): Prop := exists q, (path unit s p q) /\ isBasic unit q.

Inductive cft: pth -> Prop :=
  | cft_nil: cft nil
  | cft_f: forall p, cft (f::p)
  | cft_rec: forall n p, cft p -> cft (seq(n)::p).

Inductive hb01: pth -> pth -> Prop :=
  | hb01_seq: forall p q, cft q -> hb01 (seq(0)::p) (seq(1)::q)
  | hb01_rec: forall a p q, hb01 p q -> hb01 (a::p) (a::q).

Definition hb0(s:ustmt)(p:pth)(q:pth): Prop := hasBasicPath s p /\ hasBasicPath s q /\ hb01 p q.

Inductive precedes A: A -> A -> list A -> Prop :=
  | precedes_rec: forall a b c r, precedes A a b r -> precedes A a b (c::r)
  | precedes_base: forall a b rf rt,  precedes A a b (a::rf ++ b::rt).

Fixpoint ann2 (s:ustmt) (p:pth):ann_stmt  :=
  match s with
   | Skip x =>  Skip pth p
   | Local e x =>  Local pth e p
   | Assign l i r x => Assign pth  l i r p
   | Xfor z l u s x => Xfor pth z l u (ann2 s (p ++ ((v z)::nil))) p
   | Async s x => Async pth (ann2 s (p ++ a::nil)) p
   | Finish s x =>  Finish pth (ann2 s (p ++  f::nil)) p
   | Xseq s0 s1 x=> Xseq pth  (ann2 s0 ( p ++ (seq 0)::nil)) (ann2  s1(p ++ (seq 1)::nil)) p
end.

Definition annotate (s:ustmt) : ann_stmt :=  ann2 s nil.

Definition eq_nat : forall (x y:nat), {x=y}+{x<>y}.
Proof. decide equality. Qed.

Fixpoint substE (e:expr)(v:var)(e0:expr):expr :=
  match e with 
   | val(n) => val(n)
   | vexp(w) => if (eq_nat w v) then e0 else e
  end.

Fixpoint substS (A:Type)(s:stmt A)(v:var)(e:expr):(stmt A)  :=
  match s  with
   | Skip x =>  Skip A x
   | Local e x =>  Local A e x
   | Assign l i r x => Assign A l (substE i v e) (substE r v e) x
   | Xfor z l u s x => Xfor A z (substE l v e) (substE u v e) (substS A s v e) x
   | Async s x => Async A (substS A s v e) x
   | Finish s x =>  Finish A (substS A s v e) x
   | Xseq s0 s1 x=> Xseq A (substS A s0 v e) (substS A s1 v e) x
end.
Axiom x:var.

Inductive isAsync A: stmt A  -> Prop := 
  | isAsync_a:forall S x,  isAsync A (Async A S x)
  | isAsync_s: forall S0 S1 a, isAsync A S0 -> isAsync A S1  -> isAsync A (Xseq A S0 S1 a)
  | isAsync_X: forall S0 z l u a, isAsync A S0  -> isAsync A (Xfor _ z l u S0 a).

Inductive isSync A: stmt A  -> Prop := 
  | isSync_sk: forall a, isSync A (Skip A a)
  | isSync_local: forall e a, isSync A (Local A e a)
  | isSync_ass: forall l i r a, isSync A (Assign A l i r a)
  | isSync_a:forall S x,  isSync A (Finish A S x)
  | isSync_s0: forall S0 S1 a, isSync A S0  -> isSync A (Xseq A S0 S1 a)
  | isSync_s1: forall S0 S1 a, isSync A S1  -> isSync A (Xseq A S0 S1 a)
  | isSync_X: forall S0 z l u a, isSync A S0  -> isSync A (Xfor _ z l u S0 a).

Theorem sync_or_async: forall A S, (isSync A S) \/ (isAsync A S).  (* The same proof with more automation *)

(* A custom tactic I use very often (a bit simplified here) *)
Ltac go := 
  try congruence; 
  try econstructor (solve[go]).

Theorem sync_or_async_v2: forall A S, (isSync A S) \/ (isAsync A S).
Proof.  
  induction S; go. 
  - intuition; go. (* [intuition] will make all disjunction cases *)
  - intuition; go. 
Qed.

Theorem sync_or_async_v3: forall A S, (isSync A S) \/ (isAsync A S).
Proof.  
  induction S; intuition; go. 
Qed.

Inductive config: Type :=
  | c(a:ann_stmt)(h:heap):config
  | t(h:heap): config.


Inductive deriv: config -> config -> pth -> Prop :=
  | deriv_skip: forall p h, deriv (c(Skip pth p) h) (t h) p
  | deriv_local: forall p x h, deriv (c (Local pth x p) h) (t (loc x h)) p
  | deriv_ass: forall p l i r h, deriv (c (Assign pth l i r p) h) (t (up l i r h)) p
  | deriv_seq_l: forall r s h hh p, 
    deriv (c r h) (t hh) p -> deriv (c (Xseq pth r s p) h) (t hh) p
  | deriv_aseq: forall s r h hh p, 
    deriv (c s h) (t hh) p -> isAsync pth r -> deriv (c (Xseq pth r s p) h) (t hh) p
  | deriv_a: forall s h hh p, 
    deriv (c s h) (t hh) p -> deriv (c (Async pth s p) h) (t hh) p
  | deriv_f: forall s h hh p, 
    deriv (c s h) (t hh) p -> deriv (c (Finish pth s p) h) (t hh) p
  | deriv_for: forall s x h lo hi p, 
    lo > hi  -> deriv (c (Xfor pth x (val lo) (val hi) s p) h) (t h) p
  | deriv_a_r: forall s ss h hh p q, 
    deriv (c s h) (c ss hh) p -> deriv (c (Async pth s q) h) (c (Async pth ss q) hh) p
  | deriv_f_r: forall s ss h hh p q, 
    deriv (c s h) (c ss hh) p -> deriv (c (Finish pth s q) h) (c (Finish pth ss q) hh) p
  | deriv_seqr_l: forall r s h hh rr p q, 
    deriv (c r h) (c rr hh) p -> deriv (c (Xseq pth r s q) h) (c (Xseq pth rr s q) hh) p
  | deriv_aseqr: forall s ss r h hh p q, 
    deriv (c s h) (c ss hh) p -> isAsync pth r -> deriv (c (Xseq pth r s q) h) (c (Xseq pth r ss q) hh) p
  | deriv_for_r: forall s x h lo hi hh p, 
    lo <= hi  -> deriv (c (Xfor pth x (val lo) (val hi) s p) h) 
                               (c (Xfor pth x (val (lo+1))(val hi) (substS pth s x (val lo)) p)  hh) p
.

Inductive reduce: config -> config -> list pth -> Prop :=
  | reduce_b: forall s h p, deriv (c s h) (t h) p -> reduce (c s h) (t h) (p::nil)
  | reduce_r: forall s ss h hh hhh p ps, deriv (c s h) (c ss hh) p
                            -> reduce (c ss hh) (t hhh) ps -> reduce (c s h) (t hhh) (p::ps).

Inductive starReduce: ustmt -> heap -> list pth -> Prop := 
  | starRed: forall s h ps, reduce (c (annotate s) null) (t h) ps -> starReduce s h ps.
  
Theorem no_stuck: forall s, exists h ps, starReduce s h ps.

Lemma hb0_implies_precedence: 
  forall s p q,  hb0 s p q -> forall h ls, starReduce s h ls -> precedes pth p q ls.

Lemma precedence_implies_hb0: 
  forall s p q,  (forall h ls, starReduce s h ls -> precedes pth p q ls) -> hb0 s p q.

Theorem hb0_characterization: 
  forall s p q,  hb0 s p q <-> (forall h ls, starReduce s h ls -> precedes pth p q ls).
