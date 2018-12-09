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
