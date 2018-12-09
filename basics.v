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
End Playground1.
