Require Import ImpIO.

Local Open Scope string.
Local Open Scope list_scope.
Import Notations.
Local Open Scope impure.

Fixpoint List_iter {A} (f: A -> ?? unit) (l: list A): ?? unit :=
  match l with
  | [] => RET ()
  | a::l' => f a ;; List_iter f l' 
  end.

Lemma example: impeq (List_iter println [ Str "foo"; Str "bar"])   
                     (println "foo" ;; println "bar").
Proof.
  simpl. setoid_rewrite impeq_seq_ret_tt_r. auto.
Qed.
