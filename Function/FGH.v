(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import Coq.Arith.PeanoNat.
Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.Arithmetic.
Require Import GOO.Ordinal.Iteration.

Local Open Scope 序数符号域.

Fixpoint f (α : 序数) (n : nat) : nat :=
  match α with
  | ∅ => S n
  | α⁺ => 迭代 (f α) n n
  | lim g => f (g n) n
  end.

Fact f_3_2 : f [3] 2 = 2048.
Proof. reflexivity. Qed.

Fact f_0_n : ∀ n, f [0] n = S n.
Proof. auto. Qed.

Fact f_1_n : ∀ n, f [1] n = (n + n)%nat.
Proof.
  intros. induction n. auto.
  simpl. f_equal.
Admitted.

Fact f_ω_2 : f ω 2 = 8.
Proof. reflexivity. Qed.

Local Arguments 迭代 : simpl never.

Fact f_ωs_2 : f ω⁺ 2 = f [8] 8.
Proof. simpl. reflexivity. Qed.
