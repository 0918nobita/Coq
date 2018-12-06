(* 定数の定義 (再定義はできない) *)
Definition one : nat := 1.

(* 関数の定義 *)
Definition double x := x + x.

Print double. (* double = fun x : nat => x + x : nat -> nat *)
