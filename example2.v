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

Require Import ZArith. (* 整数モジュールのインポート *)

Module Z. (* 定義の範囲を区切るために Module を使う *)
  Open Scope Z_scope. (* 数値や演算子を整数として解釈する *)
  Eval compute in 1 - 2. (* = -1 : Z (Z は整数の型) *)
  Eval compute in (2 + 3) / 2. (* = 2 : Z *)
  Definition p (x y : Z) := 2 * x - y * y.
  Print p. (* p = fun x y : Z => 2 * x - y * y : Z -> Z -> Z *)
  Eval compute in p 3 4. (* = -10 : Z *)
  Definition p' := fun x => fun y => 2 * x - y * y.
  Print p'. (* p' = fun x y : Z => 2 * x - y * y : Z -> Z -> Z *)
  Definition q := p 3. (* 部分適用 *)
  Eval compute [p q] in q. (* p と q の定義だけを展開する *)
