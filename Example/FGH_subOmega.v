(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Export Coq.Unicode.Utf8_core.

Fixpoint 迭代 {A : Type} (F : A → A) (a : A) (n : nat) : A :=
  match n with
  | O => a
  | S n => F (迭代 F a n)
  end.

Fixpoint f (i : nat) (n : nat) : nat :=
  match i with
  | O => S n
  | S j => 迭代 (f j) n n
  end.

Fact f_0_n : ∀ n, f 0 n = S n.
Proof. reflexivity. Qed.

Fact f_1_3 : f 1 3 = f 0 (f 0 (f 0 3)).
Proof. reflexivity. Qed.

Fact f_2_3 : f 2 3 = f 1 (f 1 (f 1 3)).
Proof. reflexivity. Qed.

Compute (f 2 10).
Compute (f 3 2).

Fact f_Sn_3 : ∀ n, f (S n) 3 = f n (f n (f n 3)).
Proof. reflexivity. Qed.

Definition g n := f n n.

Definition h n := 迭代 g n n.
