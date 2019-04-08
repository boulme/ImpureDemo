Require Import ImpExtern.

Import ListNotations.

Local Open Scope list_scope.

Import Notations.
Local Open Scope impure.

Module TestNat.



(* Example of using a hash-Cons function *)

Section Building. (* Here, we only build hashed values *)

(* This hash-Cons function is shared between several function handling hashed values *)

Variable hC: pre_hashV nat -> ?? hashV nat.

Hypothesis hC_correct: forall n, WHEN hC n ~> n' THEN pre_data n=data n'.

(* First, we wrap constructors for hashed values !*)

Definition hO: unit -> ?? hashV nat := 
  fun _ =>
    hC {| pre_data := 0; hcodes := [] ; debug_info := None |}.

Lemma hO_correct: 
  WHEN hO tt ~> n THEN (data n)=O.
Proof.
  wlp_simplify.
Qed.
Global Opaque hO.
Hint Resolve hO_correct: wlp.

Definition hS: hashV nat -> ?? hashV nat :=
  fun x => 
    hC {| pre_data :=S (data x); hcodes := [hid x]; debug_info := None |}.

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




(* Now, we build the hash-Cons value from a "hash_eq".

Informal specification: 
  [hash_eq] must be consistent with the "hashed" constructors defined above.

We expect that pre_hashV values in the code of these "hashed" constructors verify:

  (hash_eq (pre_data x) (pre_data y) ~> true) <-> (hcodes x)=(hcodes y)    

*)

Definition hash_eq (x y: nat): ?? bool := 
  match x, y with
  | S x', S y' => phys_eq x' y'
  | O, O => RET true
  | _, _ => RET false
  end.

Lemma hash_eq_correct: forall x y, WHEN hash_eq x y ~> b THEN b=true -> x=y.
Proof.
  destruct x, y; wlp_simplify; try discriminate.
Qed.
Global Opaque hash_eq.
Hint Resolve hash_eq_correct builder_correct: wlp.

Local Open Scope string_scope.

Definition pretty_pre_hashV {A} (k: pstring -> ?? A) (x: pre_hashV nat) : ?? A :=
  match pre_data x, hcodes x with
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
  DO ko <~ hash_eq x y ;;
  assert_b (negb ko) "not supposed to be hash_eq, but only =";;
  DO hco <~ hCons hash_eq (pretty_pre_hashV (fun v => RET (unknownHash_msg +; " in " +; v)));;
  println "builder1";;
  DO x' <~ builder (hC hco) x;;
  next_log hco "ending builder1";;
  println "builder2";;
  DO y' <~ builder (hC hco) y;;
  next_log hco "ending builder2";;
  println "eq_test";;
  DO ok <~ phys_eq x' y' ;;
  assert_b ok "inputs are supposed to be =";;
  let k := S (max x y) in
  println "builder3";;
  builder (if fail then (hC_known hco) else (hC hco)) k;;
  next_log hco "ending builder3";;
  println "SUCCESS of example";;
  println "PRINT the table:" ;;
  DO exp <~ export hco tt ;;
  iterall exp (fun o hid d =>
  print_head o;;
  DO s <~ string_of_hashcode hid ;;
  print ((CamlStr s) +; ": ");;
  pretty_pre_hashV println d)
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

Separate Extraction BinInt TestNat.

