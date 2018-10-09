Require Export ImpExtern.
Require Extraction.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.

Import Notations.
Local Open Scope impure.

(* We can emulate polymorphic references in Coq only with external functions and products *)

Record cref {A} := {
  set: A -> ?? unit;
  get: unit -> ?? A
}.
Arguments cref: clear implicits.

Axiom make: forall {A}, A -> ?? cref A.
Extract Constant make => "(fun x -> let r = ref x in { set = (fun y -> r:=y); get = (fun () -> !r) })".

Local Open Scope nat_scope.


Module TestNat.

(* Now, we can embed invariants into these Coq references 

Here is a tiny example...

*)

Record mydata := {
  history: list nat;
  the_max: nat;
  the_max_in_history: List.In the_max history;
  the_max_is_max: forall x, List.In x history -> x <= the_max
}.

Program Definition single x : ?? cref (mydata) := 
  make {| history:= x::nil; the_max := x |}.
Obligation 2.
  intuition subst; auto.
Qed.


Program Definition add v (r: cref mydata): ?? unit :=
  DO d <~ get r ();;
  set r {| history:=v::(history d); the_max := max v (the_max d) |}.
Obligation 1.
  destruct d; simpl; apply Nat.max_case_strong; auto.
 Qed.
Obligation 2.
  destruct d; simpl in * |- *; apply Nat.max_case_strong; intuition.
  lapply (the_max_is_max0 x); auto. omega.
Qed.

(*
Remark that in Coq, we only deduce informations from the type ! 
In particular, we can not prove that

  [set r x;; get r ()] will return [x].

Indeed, this is false for another implementation of make:

  [(fun x -> let r = ref x in { set = (fun y -> r:=y); get = (fun () -> x) })

More generally, I can not prove anything about "get" except that if it returns a value then the value inhabits its type.

Here, be aware that we can define aliases in Coq, even if can not reason about them.

*)

Definition example_Jaber {A} (x: cref A) (y: cref mydata) : ?? A :=
  DO rd0 <~ single 0;;
  DO d0 <~ get rd0 ();;
  set y d0;;
  get x ().

Program Definition alias_example (r1: cref mydata) : ?? nat := 
  DO r2 <~ make (exist (fun r => r = r1) r1 _);; (* r2: cref {r : cref mydata | r = r1} *)
  DO r <~ example_Jaber r2 r1;; 
  ASSERT ((`r)=r1);; (* this is proved automatically ! *)
  DO d <~ get r ();;
  RET (the_max d). (* But, we can not prove that the returned value is [0] *) 

(* Now, the issues are the following:

1) will the OCaml extraction of the Coq code be sound with the properties proved ?
2) is it possible to find a well-typed OCaml implementation of [make] of type 'a -> 'a cref
   which breaks some invariant proved in Coq.

*)


Local Open Scope string_scope.

Definition test: ?? unit :=
  DO r1 <~ single 10 ;;
  DO v <~ alias_example r1;;
  assert_b (Nat.eqb v 0) "Ok: we can not prove this. It depends on the implementation of make.";;
  RET tt.


End TestNat.


(*************************)
(* Extraction directives *)

Require Import ExtrOcamlString.
Require Import ExtrOcamlBasic.

Import ImpConfig.

Extraction Blacklist List String.

Separate Extraction BinIntDef ImpExtern TestNat.
