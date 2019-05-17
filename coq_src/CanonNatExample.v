Require Import ImpExtern.

Import ListNotations.

Local Open Scope list_scope.

Import Notations.
Local Open Scope impure.

Import HConsing.

Module TestNat.

(* Example of using a hash-Cons function *)

Section Building. (* Here, we only build hashed values *)

(* This hash-Cons function is shared between several function handling hashed values *)

Variable hC: hashinfo (hashV nat) -> ?? hashV nat.

Hypothesis hC_correct: forall n, WHEN hC n ~> n' THEN data (hdata n)=data n'.

(* First, we wrap constructors for hashed values !*)

Definition hO: unit -> ?? hashV nat := 
  fun _ =>
    hC {| hdata := liftHV 0; hcodes := [] ; debug_info := None |}.

Local Hint Resolve hC_correct.

Lemma hO_correct: 
  WHEN hO tt ~> n THEN (data n)=O.
Proof.
  wlp_simplify.
Qed.
Global Opaque hO.
Hint Resolve hO_correct: wlp.

Definition hS: hashV nat -> ?? hashV nat :=
  fun x => 
    hC {| hdata :=liftHV (S (data x)); hcodes := [hid x]; debug_info := None |}.

Lemma hS_correct n: 
  WHEN hS n ~> n' THEN (data n')=(S (data n)).
Proof.
  wlp_simplify.
Qed.
Global Opaque hS.
Hint Resolve hS_correct: wlp.

(* Second, we use these hashed constructors ! *)

Fixpoint builder (x:nat): ?? hashV nat :=
  match x with
  | O => hO tt
  | S n => 
    DO n' <~ builder n;;
    (* print "*";; *)
    hS n'
  end.

Lemma builder_correct:
   forall x, WHEN builder x ~> x' THEN x=(data x').
Proof.
  induction x; simpl; wlp_simplify.
Qed.
Global Opaque builder.

End Building.



(* Now, we build the hash-Cons value from a "hasheq".

Informal specification: 
  [hash_eq] must be consistent with the "hashed" constructors defined above.

We expect that hashinfo values in the code of these "hashed" constructors verify:

  (hasheq (data (hdata x)) (data (hdata y)) ~> true) <-> (hcodes x)=(hcodes y)

*)

Definition hasheq (x y: nat): ?? bool :=
  match x, y with
  | S x', S y' => phys_eq x' y'
  | O, O => RET true
  | _, _ => RET false
  end.

Lemma hasheq_correct: forall x y, WHEN hasheq x y ~> b THEN b=true -> x=y.
Proof.
  destruct x, y; wlp_simplify; try discriminate.
Qed.
Global Opaque hasheq.

Hint Resolve hasheq_correct builder_correct: wlp.


Local Open Scope string_scope.
Definition pretty_hashinfo {A} (k: pstring -> ?? A) (x: hashinfo (hashV nat)) : ?? A :=
  match data (hdata x), hcodes x with
  | 0, _ => k "O"
  | S n, [nid] =>
      DO s <~ string_of_hashcode nid ;;
      k ("S " +; (CamlStr s))
  | _, _ => FAILWITH "unexpected hcodes"
  end.

Definition unknownHash_msg: pstring := "unknown hashed value".

Fixpoint print_head (head: list pstring): ?? unit :=
  match head with
  | s::head' => println ("- " +; s);; print_head head'
  | _ => RET tt
  end.

Definition example (x y: nat) (fail: bool): ?? unit :=
  println "START example";;
  DO ko <~ hasheq x y ;;
  assert_b (negb ko) "not supposed to be hash_eq, but only =";;
  DO hco <~ hConsV hasheq;;
  println "builder1";;
  DO x' <~ builder (hC hco) x;;
  next_log hco "ending builder1";;
  println "builder2";;
  DO y' <~ builder (hC hco) y;;
  next_log hco "ending builder2";;
  println "eq_test";;
  DO ok <~  phys_eq x' y' ;;
  assert_b ok "inputs are supposed to be =" ;;
  let k := S (max x y) in
  println "builder3";;
  let hC_known := hC_known hco (pretty_hashinfo (fun v => RET (unknownHash_msg +; " in " +; v))) in
  builder (if fail then hC_known else (hC hco)) k;;
  next_log hco "ending builder3";;
  println "SUCCESS of example";;
  println "PRINT the table:" ;;
  DO exp <~ export hco tt ;;
  iterall exp (fun o hid d =>
  print_head o;;
  DO s <~ string_of_hashcode hid ;;
  print ((CamlStr s) +; ": ");;
  pretty_hashinfo println d)
  .

Definition example_correct x y fail:
  WHEN example x y fail ~> _ THEN x=y.
Proof.
  wlp_simplify.
Qed.

Definition test_example x y fail: ?? unit :=  
  println "";;
  TRY
     example x y fail
  WITH_FAIL s, e => 
     println ("FAILURE of example: " +; s).

Local Open Scope nat.

Fixpoint dup (x:nat): nat :=
  match x with
  | O => O
  | S n => S (dup n) 
  end.

Definition test: ?? unit :=
  let n:=100 in
  test_example n n false;;
  test_example (S (S n)) n false;;
  test_example n (dup n) true;;
  test_example n (dup n) false.

End TestNat.


(*************************)
(* Extraction directives *)

Require Import ExtrOcamlString.
Require Import ExtrOcamlBasic.

Import ImpConfig.

Extraction Blacklist List String.

Separate Extraction BinInt ImpPrelude TestNat.

