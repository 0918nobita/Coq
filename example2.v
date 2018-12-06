(* 定数の定義 (再定義はできない) *)
Definition one : nat := 1.

(* 関数の定義 *)
Definition double x := x + x.

Print double. (* double = fun x : nat => x + x : nat -> nat *)

Eval compute in double 2. (* = 4 : nat (式の計算) *)

(* 局所的な名前束縛 *)
Definition quad x := let y := double x in 2 * y.
Eval compute in quad 2. (* = 8 : nat *)

Definition quad' x := double (double x).
Eval compute in quad' 2.

Definition triple x :=
  let double x := x + x in
  double x + x.

Eval compute in triple 3. (* = 9 : nat *)
Eval compute in 1 - 2. (* = 0 : nat (自然数の引き算は整数と違う) *)
