(* 自然数モジュールのインポート *)
Require Import Arith.

(* 関数定義 *)
Definition f x := x + 100.
Definition g x := x - 100.

(* 証明開発モード *)
Theorem g_f : forall x, g (f x) = x.
Proof.
  intros x.
  unfold f, g.
  rewrite Nat.add_sub.
  reflexivity.
Qed.
