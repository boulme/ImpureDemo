Require Export ImpExtern.
Require Extraction.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.

Import Notations.
Local Open Scope impure.


Local Open Scope nat_scope.


Module TestNat.

(* Now, we can embed invariants into these Coq references 

Here is a tiny example...

*)

(*
Remark that in Coq, we only deduce informations from the type ! 
In particular, we can not prove that

  [set r x;; get r ()] will return [x].

Indeed, this is false for another implementation of make:

  [(fun x -> let r = ref x in { set = (fun y -> r:=y); get = (fun () -> x) })

More generally, I can not prove anything about "get" except that if it returns a value then the value inhabits its type.

Here, be aware that we can define aliases in Coq, even if can not reason about them.

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
  | 0 => RET ()
  | S p => k () ;; repeat p k
  end.

Definition hello (s:pstring): ?? unit :=
  repeat 3 (fun _ => println s).

(* wrong repeat *)
Fixpoint wrepeat (n:nat) (k: ?? unit): ?? unit :=
  match n with
  | 0 => RET ()
  | S p => k ;; wrepeat p k
  end.

Definition whello (s:pstring): ?? unit :=
  wrepeat 3 (println s).

Lemma wrong_IO_reasoning (s:pstring):
  (hello s)=(whello s).
Proof.
  unfold hello, whello; simpl. auto.
Qed.

Definition interactive: bool := false.

Definition test2: ?? unit :=
  DO s <~ 
   (if interactive then (
      print("Enter a line: ");;
      read_line()
   ) else RET (Str "hello"));;
  println("version 1");;
  hello s;;
  println("version 2");;
  whello s.

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

Separate Extraction BinIntDef ImpExtern TestNat.
