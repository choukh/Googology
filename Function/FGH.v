(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.WellFormed.
Require Import GOO.Ordinal.Recursion.
Require Import GOO.Ordinal.Arithmetic.
Require Import GOO.Ordinal.Iteration.
Require Import GOO.Ordinal.VeblenFunction.
Require GOO.Ordinal.ExtendedVeblenFunction.

Local Open Scope 序数域.

Fixpoint f (α : 序数) (n : nat) : nat :=
  match α with
  | ∅ => S n
  | α⁺ => 迭代 (f α) n n
  | lim g => f (g n) n
  end.

Fact f_0_n : ∀ n, f [0] n = S n.
Proof. easy. Qed.

Lemma 迭代_f0_Sn_m : ∀ n m, 迭代 S (S n) m = S (迭代 S n m).
Proof. intros. induction m. easy. simpl. f_equal. apply IHm. Qed.

Theorem f_1_n : ∀ n, f [1] n = 2 * n.
Proof.
  induction n. easy. simpl.
  f_equal. rewrite 迭代_f0_Sn_m, Nat.add_succ_r.
  f_equal. apply IHn.
Qed.

Lemma f_Sn_m : ∀ n m, f [S n] m = 迭代 (f [n]) m m.
Proof. easy. Qed.

Lemma 迭代_g_n_Sm : ∀ g (n m : nat), 迭代 g n (S m) = g (迭代 g n m).
Proof. easy. Qed.

Lemma 迭代_f1_Sn_m : ∀ n m, 迭代 (f [1]) (S n) m = 2 ^ m * (S n).
Proof.
  intros. induction m. simpl. lia.
  rewrite 迭代_g_n_Sm, f_1_n, IHm. simpl. lia.
Qed.

Theorem f_2_n : ∀ n, f [2] n = 2 ^ n * n.
Proof.
  intros. destruct n. easy.
  rewrite f_Sn_m, 迭代_g_n_Sm, f_1_n, 迭代_f1_Sn_m. simpl. lia.
Qed.

Fact f_3_2 : f [3] 2 = 2048.
Proof. reflexivity. Qed.

Fact f_ω_2 : f ω 2 = 8.
Proof. reflexivity. Qed.

Local Arguments 迭代 : simpl never.

Fact f_Sω_2 : f ω⁺ 2 = f [8] 8.
Proof. simpl. reflexivity. Qed.

Module 算术层级.
Import FunctionalExtensionality.
Local Open Scope 序数算术域.

Lemma 加于零 : ∀ α, [0] + α = α.
Proof.
  induction α as [|α IH|f IH]. reflexivity.
  - rewrite 加后继, IH. easy.
  - rewrite 加极限. f_equal. apply functional_extensionality. apply IH.
Qed.

Lemma ω2表示为迭代 : ω * [2] = Itω 后继 ω.
Proof.
  unfold 乘法. rewrite <- 有穷迭代等于有限递归.
  unfold 迭代. rewrite 加于零.
  unfold 加法, Itω. simpl. f_equal. apply functional_extensionality.
  intros n. rewrite 有穷迭代等于有限递归. easy.
Qed.

Lemma ω加n表示为迭代 : ∀ n, ω + [n] = 迭代 后继 ω n.
Proof. induction n. easy. simpl. rewrite 加后继, IHn. easy. Qed.

Theorem f_ω2_n : ∀ n, f (ω * [2]) n = f (ω + [n]) n.
Proof. intros. rewrite ω2表示为迭代, ω加n表示为迭代. easy. Qed.

End 算术层级.

Lemma f_极限 : ∀ g n, f (lim g) n = f (g n) n.
Proof. reflexivity. Qed.

Module 二元Veblen层级.
Import VeblenFunction.二元.

Fact f__φ_0_0__2 : f (φ [0] [0]) 2 = 4.
Proof. reflexivity. Qed.

Fact f__φ_0_1__2 : f (φ [0] [1]) 2 = 8.
Proof. reflexivity. Qed.

Fact f__φ_1_0__2 : f (φ [1] [0]) 2 = 8.
Proof. reflexivity. Qed.

Fact f__φ_1_1__2 : f (φ [1] [1]) 2 = f (cantor ∅ (cantor ∅ (φ [1] [0])⁺)) 2.
Proof. simpl. reflexivity. Qed.

Fact f__φ_2_0__2 : f (φ [2] [0]) 2 = f (φ [1] (φ [1] [0])) 2.
Proof.
  unfold φ. simpl veblen.
  unfold 不动点枚举 at 1. simpl 递归.
  unfold 最小不动点, 无穷迭代. rewrite f_极限.
  unfold 迭代. reflexivity.
Qed.

Fact f__Γ_0__2 : f (Γ [0]) 2 = 8.
Proof. reflexivity. Qed.

Fact f__Γ_0__3 : f (Γ [0]) 3 = f (φ (φ (φ [0] [0]) [0]) [0]) 3.
Proof.
  unfold Γ, 不动点枚举. simpl 递归.
  unfold 最小不动点, 无穷迭代. rewrite f_极限.
  unfold 迭代. reflexivity.
Qed.

Fact f__Γ_1__2 : f (Γ [1]) 2 = f (φ (φ (Γ [0])⁺ [0]) [0]) 2.
Proof.
  unfold Γ, 不动点枚举. simpl 递归.
  unfold 后继不动点, 无穷迭代. rewrite f_极限.
  unfold 迭代. reflexivity.
Qed.

End 二元Veblen层级.

Module 三元Veblen层级.
Import VeblenFunction.三元.

Fact f__φ_0_0_1__2 : f (φ [0] [0] [1]) 2 = 8.
Proof. reflexivity. Qed.

Fact f__φ_0_1_0__2 : f (φ [0] [1] [0]) 2 = 8.
Proof. reflexivity. Qed.

Fact f__φ_1_0_0__2 : f (φ [1] [0] [0]) 2 = 8.
Proof. reflexivity. Qed.

Fact f__φ_1_0_1__2 : f (φ [1] [0] [1]) 2 = f (二元.Γ [1]) 2.
Proof. reflexivity. Qed.

Fact f__φ_1_1_0__2 : f (φ [1] [1] [0]) 2 = f (二元.ε1 [0]) 2.
Proof. reflexivity. Qed.

Fact f__φ_2_0_0__2 : f (φ [2] [0] [0]) 2 = f (二元.Γ1 [0]) 2.
Proof. reflexivity. Qed.

End 三元Veblen层级.

Module 四元Veblen层级.
Import VeblenFunction.四元.

Fact f__φ_0_0_0_1__2 : f (φ [0] [0] [0] [1]) 2 = 8.
Proof. reflexivity. Qed.

Fact f__φ_0_0_1_0__2 : f (φ [0] [0] [1] [0]) 2 = 8.
Proof. reflexivity. Qed.

Fact f__φ_0_1_0_0__2 : f (φ [0] [1] [0] [0]) 2 = 8.
Proof. reflexivity. Qed.

Fact f__φ_1_0_0_0__2 : f (φ [1] [0] [0] [0]) 2 = 8.
Proof. reflexivity. Qed.

Fact f__φ_1_0_0_1__2 : f (φ [1] [0] [0] [1]) 2 = f (三元.φ (三元.φ ((φ [1] [0] [0] [0])⁺) ∅ ∅) ∅ ∅) 2.
Proof.
  unfold φ. simpl veblen.
  unfold 不动点枚举 at 1. simpl 递归.
  unfold 后继不动点, 无穷迭代. rewrite f_极限.
  unfold 迭代. reflexivity.
Qed.

Fact f__φ_1_0_0_2__2 : f (φ [1] [0] [0] [2]) 2 = f (三元.φ (三元.φ ((φ [1] [0] [0] [1])⁺) ∅ ∅) ∅ ∅) 2.
Proof.
  unfold φ. simpl veblen.
  unfold 不动点枚举 at 1. simpl 递归.
  unfold 后继不动点, 无穷迭代. rewrite f_极限.
  unfold 迭代. reflexivity.
Qed.

Fact f__φ_1_0_0_ω__2 : f (φ [1] [0] [0] ω) 2 = f (φ [1] [0] [0] [2]) 2.
Proof.
  unfold φ. simpl veblen.
  unfold 不动点枚举 at 1. simpl 递归.
  rewrite f_极限. reflexivity.
Qed.

Fact f__φ_1_0_0_φ_1_0_0_0__2 : f (φ [1] [0] [0] (φ [1] [0] [0] [0])) 2 =
  f (φ [1] [0] [0] (三元.φ (三元.φ ∅ ∅ ∅) ∅ ∅)) 2.
Proof.
  unfold φ. simpl veblen.
  unfold 不动点枚举. simpl 递归.
  rewrite f_极限. simpl 递归. reflexivity.
Qed.

Fact f__φ_1_0_1_0__2 : f (φ [1] [0] [1] [0]) 2 = f (φ [1] [0] [0] (φ [1] [0] [0] [0])) 2.
Proof.
  unfold φ. simpl veblen.
  unfold 不动点枚举 at 1. simpl 递归.
  unfold 最小不动点, 无穷迭代. rewrite f_极限.
  unfold 迭代. reflexivity.
Qed.

Fact f__φ_1_1_0_0__2 : f (φ [1] [1] [0] [0]) 2 = f (φ [1] [0] (φ [1] [0] [0] [0]) [0]) 2.
Proof.
  unfold φ. simpl veblen.
  unfold 不动点枚举 at 1. simpl 递归.
  unfold 最小不动点, 无穷迭代. rewrite f_极限. reflexivity.
Qed.

Fact f__φ_2_0_0_0__2 : f (φ [2] [0] [0] [0]) 2 = f (φ [1] (φ [1] [0] [0] [0]) [0] [0]) 2.
Proof.
  unfold φ. simpl veblen.
  unfold 不动点枚举 at 1. simpl 递归.
  unfold 最小不动点, 无穷迭代. rewrite f_极限. reflexivity.
Qed.

End 四元Veblen层级.

Import ExtendedVeblenFunction.

Fact f_SVO_0 : f SVO 0 = 1.
Proof. reflexivity. Qed.

Fact f_SVO_1 : f SVO 1 = 2.
Proof. reflexivity. Qed.

Fact f_SVO_2 : f SVO 2 = 8.
Proof. reflexivity. Qed.

Fact f_SVO_n : ∀ n, f SVO n = f (φ n [1] ∅..) n.
Proof. reflexivity. Qed.
