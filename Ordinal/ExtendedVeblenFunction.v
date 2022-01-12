(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.Operation.
Require Import GOO.Ordinal.Recursion.
Require Import GOO.Ordinal.Arithmetic.
Require Import GOO.Ordinal.Iteration.
Require Import GOO.Ordinal.EpsilonNumbers.
Require Import GOO.Ordinal.VeblenFunction.

Local Open Scope 序数域.

Fixpoint 多元函数 n {T} :=
  match n with
  | O => T
  | S n => 序数 → @多元函数 n T
  end.

Fixpoint 充零 {n} (f : 多元函数 n) : 序数 :=
  match n, f with
  | O, f => f
  | S m, f => 充零 (f ∅)
  end.

Fixpoint 换首元 {n} (f : nat → @多元函数 n 序数) : @多元函数 n (nat → 序数) :=
  match n, f with
  | O, f => f
  | S m, f => λ α, 换首元 (λ n, f n α)
  end.

Fixpoint 多元极限 {n} (f : @多元函数 n (nat → 序数)) : @多元函数 n 序数 :=
  match n, f with
  | O, f => lim f
  | S m, f => λ α, 多元极限 (f α)
  end.

Fixpoint veblen {n} (f : 多元函数 (S n)) : 多元函数 (S (S n)) :=
  let fix inner (f : 多元函数 (S n)) (α : 序数) : 多元函数 (S n) :=
    match α with
    | ∅ => f
    | α⁺ => let fix 增元迭代 (f₁ : 多元函数 1) n : 多元函数 (S n) :=
      match n with
      | O => f₁
      | S m => veblen (增元迭代 f₁ m)
      end in 增元迭代 (λ β, 充零 (inner f α β))′ n
    | lim g => 多元极限 (换首元 (λ n, inner f (g n)))
    end in inner f.

Definition φ n : 多元函数 n :=
  match n with
  | O => ∅
  | S m => let fix inner n : 多元函数 (S n) :=
    match n with
    | O => cantor ∅
    | S m => veblen (inner m)
    end in inner m
  end.

Definition SVO := lim (λ n, 充零 (φ (S n) [1])).

Fact φ_0 : φ 0 = ∅.
Proof. reflexivity. Qed.

Fact φ_1_α : ∀ α, φ 1 α = cantor ∅ α.
Proof. reflexivity. Qed.

Fact φ_2_α_β : ∀ α β, φ 2 α β = 二元.φ α β.
Proof. reflexivity. Qed.

Fact φ_3_α_β : ∀ α β γ, φ 3 α β γ = 三元.φ α β γ.
Proof. reflexivity. Qed.

Fact φ_4_α_β : ∀ α β γ δ, φ 4 α β γ δ = 四元.φ α β γ δ.
Proof. reflexivity. Qed.
