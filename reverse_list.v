Require Import List.
Import ListNotations.

(* 再帰関数の定義 *)
Fixpoint reverse {A : Type} (xs : list A) :=
  match xs with
  | nil => nil
  | x :: xs' =>
    reverse xs' ++ [x]
  end.

Compute reverse [1; 2; 3]. (* = [3; 2; 1] : list nat *)

(* 補題 *)
Lemma reverse_append : forall (A : Type) (xs ys : list A),
  reverse (xs ++ ys) = reverse ys ++ reverse xs.
Proof.
  intros A xs ys.
  induction xs.
- simpl.
  rewrite app_nil_r.
  reflexivity.
- simpl.
  rewrite IHxs.
  rewrite app_assoc.
  reflexivity.
Qed.

Theorem reverse_reverse : forall (A : Type) (xs : list A),
  reverse (reverse xs) = xs.
Proof.
  intros A xs.
  induction xs.
- simpl.
  reflexivity.
- simpl.
  rewrite reverse_append.
  simpl.
  rewrite IHxs.
  reflexivity.
Qed.
