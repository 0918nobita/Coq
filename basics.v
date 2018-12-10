(* 新しいデータ型のセット (集合) である「列挙型」 *)
Inductive day: Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

(* 関数定義 *)
Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

(* [関数定義が正しいことをチェックする] *)

(* 方法1. simpl: (simplify) 与えた式を正確に評価する *)
Eval simpl in (next_weekday (next_weekday saturday)).

(* 方法2. 確認事項に名前を与える *)
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof.
  simpl.
  reflexivity.
Qed. (* 確認事項は、簡約後の同値チェックによって証明された *)

(* 方法3. Coq で定義したものから、他のより一般的な言語のプログラムを抽出する *)

(* ブール型 (ここでは標準ライブラリを利用せずに自作する) *)
Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2 : (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb3 : (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4 : (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Definition admit {T : Type} : T. Admitted.

Definition nandb (b1 b2 : bool) : bool := negb (andb b1 b2).

Example test_nandb1 : (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2 : (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3 : (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4 : (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1 b2 b3 : bool) : bool := andb (andb b1 b2) b3.

Example test_andb31 : (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32 : (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33 : (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34 : (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* 式の型を表示する *)
Check (negb true). (* negb true : bool *)
Check negb. (* negb : bool -> bool *)
Check andb3. (* andb3 : bool -> bool -> bool -> bool *)

Module Playground1.
  Inductive nat : Type :=
    | O : nat         (* O は自然数 *)
    | S : nat -> nat. (* S は自然数を引数に取り、別の自然数を生成する「コンストラクタ」 *)
                      (* n が自然数なら S n も自然数 *)
  (* 今まで定義してきた帰納的な型は、実際には式の集合と言うべきもの *)
  (* nat の定義は、nat の要素となる式がどのように構築されるかを表している *)

  Definition pred (n : nat) : nat := (* S とは違って「計算ルール」を示している *)
    match n with
      | O => O
      | S n' => n'
    end.
  Check S. (* S : nat -> nat *)
  Check pred. (* pred : nat -> nat *)
End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))). (* 4 : nat *)
Eval simpl in (minustwo 4). (* 2 : nat *)
Check minustwo. (* minustwo : nat -> nat *)

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool := negb (evenb n).

Example test_oddb1 : (oddb (S O)) = true.
Proof. simpl. reflexivity. Qed.

Example test_oddb2 : (oddb (S(S(S(S( O)))))) = false.
Proof. simpl. reflexivity. Qed.

Module Playground2.
  Fixpoint plus (n m : nat) : nat :=
    match n with
      | O => m
      | S n' => S (plus n' m)
    end.
  Eval simpl in (plus (S (S (S O))) (S (S O))). (* 5 : nat *)

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
      | O, _ => O
      | S _, O => n
      | S n', S m' => minus n' m'
    end.

  Fixpoint mult (n m : nat) : nat :=
    match n with
      | O => O
      | S n' => plus m (mult n' m)
    end.

  Example test_mult1 : (mult 3 3) = 9.
  Proof. simpl. reflexivity. Qed.
End Playground2.

(* 指数関数 *)
Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Example test_exp : (exp 2 3) = 8.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n : nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1 : (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2 : (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Eval simpl in 2 + 3 * (8 - 4). (* 14 : nat *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n', S m' => beq_nat n' m'
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n, m with
    | O, _ => true
    | S _, O => false
    | S n', S m' => ble_nat n' m'
  end.

Example test_ble_nat1 : (ble_nat 2 2) = true.
Proof. simpl. reflexivity. Qed.

Example test_ble_nat2 : (ble_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_ble_nat3 : (ble_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool := andb (negb (beq_nat n m)) (ble_nat n m).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* 簡約による証明 *)
Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof. simpl. reflexivity. Qed.

Theorem plus_0_n' : forall n : nat, 0 + n = n.
Proof. reflexivity. Qed.

(* Example, Theorem, Lemma, Fact, Remark コマンドの挙動は同じ *)

Eval simpl in (forall n : nat, n + 0 = n). (* forall n : nat, n + 0 = n : Prop (命題) *)
Eval simpl in (forall n : nat, 0 + n = n). (* forall n : nat, n = n : Prop (簡約されている) *)

(* intros タクティック : 量化子や仮定をゴールから前提条件に変える *)
Theorem plus_0_n'' : forall n : nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof. intros n. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof. intros n. reflexivity. Qed.
(* l := left *)

Theorem plus_id_example : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  intros n m H.
  rewrite H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o H H2.
  rewrite H.
  rewrite H2.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_0_n.
  reflexivity.
Qed.

Theorem mult_1_plus : forall n m : nat,
  (1 + n) * m = m + (n * m).
Proof.
  intros n m.
  rewrite -> plus_1_l.
  simpl.
  reflexivity.
Qed.
