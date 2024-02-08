(** Example of type unsafety by linking impure OCaml code and Coq extracted code -
    WITHOUT Impure.

    Ideas from David Monniaux and Matthieu Sozeau.
*)

Definition bool_or_nat (b: bool) :=
  if b then bool else nat.

Definition else3 (b: bool) : (bool_or_nat b) :=
  match b with
  | true => true
  | false => 3
  end.

Definition xcombine(b : bool):  (bool_or_nat b) -> nat :=
  match b with
  | true => fun x => 0
  | false => fun x => x+x
  end.

Require Import Extraction.
Extraction Inline xcombine else3.

Module TypeUnsafety.

Axiom bad_choice : unit -> bool.
Extract Constant bad_choice => "(let b = ref true in fun () -> let r = !b in b := false; Printf.printf ""%b"" r; print_newline(); r)".

(* This type unsafety causes a segmentation fault (with byte compilation). *)
Definition bug := 
  let arg := bad_choice tt in
  xcombine (bad_choice tt) (else3 arg).

End TypeUnsafety.



Require Import ImpExtern.
Import Notations.
Local Open Scope impure.


(* Adapting the bug above in the Impure monad *)

Module FixedSafety.

Axiom bad_choice : unit -> ?? bool.
Extract Constant bad_choice => "(let b = ref true in fun () -> let r = !b in b := false; Printf.printf ""%b"" r; print_newline(); r)".

(* Cannot typecheck
Definition bug := 
  DO arg1 <~ bad_choice tt;;
  DO arg2 <~ bad_choice tt;;
  RET (xcombine arg2 (else3 arg1)).
*)

(* coerce bad_choice into a pure computation: safe_coerce raises an exception if the Boolean is false. *)
Definition choice (x:unit): bool := safe_coerce (bad_choice x) "bad_choice has returned false".

(* here the bug appears as an clean exception ! *)
Definition bug :=
  let arg1 := choice tt in
  let arg2 := choice tt in
  xcombine arg2 (else3 arg1).

End FixedSafety.

(*************************)
(* Extraction directives *)

Require Import ExtrOcamlString.
Require Import ExtrOcamlBasic.

Extraction Blacklist List String.

Separate Extraction BinInt ImpExtern TypeUnsafety FixedSafety. (* comments TypeUnsafety in order to see run the bug in FixedSafety *)
