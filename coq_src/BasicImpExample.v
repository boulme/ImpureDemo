(** Very basic examples of embedding imperative features in Coq through the Impure library *)

Require Export ImpExtern.
Require Extraction.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.

Import Notations.
Local Open Scope impure.


Local Open Scope nat_scope.


(* a trivial example of WLP reasoning *)
Section TRIV_WLP.

Variable f: nat -> ?? nat.

Definition g (x:nat): ?? nat :=
 DO r <~ f x;;
 RET (r+1).

Lemma triv: forall x, WHEN g x ~> r THEN r > 0.
Proof.
  wlp_simplify. lia.
Qed.

End TRIV_WLP.


(* Examples showing that cyclic values must be forbidden on extraction of inductive types *)

Section Issue_with_cyclic_value.

Inductive empty: Type:= Absurd: empty -> empty.

Lemma never_return_empty (f: unit -> ??empty):
  WHEN f () ~> _ THEN False.
Proof.
  wlp_simplify.
  clear Hexta.
  induction exta. auto.
Qed.
(* issue: in OCaml, the extraction of type [empty] is currently inhabited by a cyclic value *)


Definition is_zero (n:nat): bool :=
  match n with
  | O => true
  | _ => false
  end.


Lemma is_zero_correct n: is_zero n = true <-> n = 0.
Proof.
  destruct n; simpl; intuition.
Qed.


Lemma phys_eq_pred n: WHEN phys_eq (pred n) n ~> b THEN b=true -> (is_zero n)=true.
Proof.
  wlp_simplify.
  rewrite is_zero_correct; clear exta Hexta H0.
  generalize H1; clear H1; induction n; simpl; auto.
  intros H1; rewrite <- H1. apply IHn; clear IHn.
  destruct n; simpl; auto.
Qed.
(* issue: in OCaml, the extraction of type [nat] is currently inhabited by a cyclic value [fuel] 
   such that [pred fuel == fuel] returns [true] and [is_zero fuel] returns [false].  *)

End Issue_with_cyclic_value.


Section Pseudo_Identity.

Variable pid: forall A, A->??A.

Program Definition cpid {B} (x:B): ?? B :=
  DO z <~ pid { y | y = x } x ;;
  RET `z.

Lemma cpid_correct A (x y:A):
  WHEN (cpid x) ~> y THEN  y=x.
Proof.
  wlp_simplify. destruct exta; subst; auto.
Qed.

End Pseudo_Identity.



Module TestNat.

(* Now, we embed invariants into Coq references 

Here is a tiny example...

*)

(*
Remark that in Coq, we only deduce informations from the type ! 
In particular, we can not prove that

  [set r x;; get r ()] will return [x].

Indeed, this is false for another implementation of make:

  [(fun x -> let r = ref x in { set = (fun y -> r:=y); get = (fun () -> x) })

More generally, I can not prove anything about "get" except that if it returns a value then the value inhabits its type.

Here, be aware that we can define aliases in Coq, even if we cannot reason about them.

*)

Definition may_alias{A} (x:cref A) (y:cref nat):?? A:=
  y.(set) 0;;
  x.(get) ().

Program Definition alias_example (r1: cref nat) : ?? nat := 
  DO r2 <~ make_cref (exist (fun r => r = r1) r1 _);; (* r2: cref {r : cref nat | r = r1} *)
  DO r <~ may_alias r2 r1;; 
  ASSERT ((`r)=r1);; (* this is proved automatically ! *)
  get r (). (* But, we can not prove that the returned value is [0] *) 

Program Definition alias_ex (r1: cref nat) : ?? { r | r=r1 } := 
  DO r2 <~ make_cref (exist (fun r => r = r1) r1 _);; 
  may_alias r2 r1.


(* Now, the issues are the following:

1) will the OCaml extraction of the Coq code be sound with the properties proved ?
2) is it possible to find a well-typed OCaml implementation of [make] of type 'a -> 'a cref
   which breaks some invariant proved in Coq.

*)

Local Open Scope string_scope.

Definition test1: ?? unit :=
  DO r1 <~ make_cref 10 ;;
  DO v <~ alias_example r1;;
  assert_b (Nat.eqb v 0) "Ok: we cannot prove this. It depends on the implementation of make.";;
  RET tt.


Record mydata := {
  value: nat;
  bounded: value > 10
}.

Lemma mydata_preserved (x: cref mydata) (y: cref nat):
  WHEN may_alias x y ~> v THEN 
    v.(value) > 10.
Proof.
  wlp_simplify. destruct exta0; simpl; auto.
Qed. 

Fixpoint repeat (n:nat) (k: unit -> ?? unit): ?? unit :=
  match n with
  | 0 => RET()
  | S p => k();; repeat p k
  end.

Definition print3 (s:pstring): ?? unit :=
  repeat 3 (fun _ => println s).

(* wrong repeat *)
Fixpoint wrepeat (n:nat) (k: ?? unit): ?? unit :=
  match n with
  | 0 => RET()
  | S p => k;; wrepeat p k
  end.

Definition wprint3 (s:pstring): ?? unit :=
  wrepeat 3 (println s).

Lemma wrong_IO_reasoning (s:pstring):
  (print3 s)=(wprint3 s).
Proof.
  unfold print3, wprint3; simpl. auto.
Qed.

Definition interactive: bool := false.

Definition test2: ?? unit :=
  DO s <~ 
   (if interactive then (
      print("Enter a line: ");;
      read_line()
   ) else RET (Str "hello"));;
  println("version 1");;
  print3 s;;
  println("version 2");;
  wprint3 s.

End TestNat.


(* An other example *)
Require Import PArith.
Check forall {A}, (list (positive*A)) -> ??((positive -> ??(option A))*(positive*A -> ??unit)).


(*************************)
(* Extraction directives *)

Require Import ExtrOcamlString.
Require Import ExtrOcamlBasic.

Import ImpConfig.

Extraction Blacklist List String.

Separate Extraction BinInt ImpExtern TestNat.
