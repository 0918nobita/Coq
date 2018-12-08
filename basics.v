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
