(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.Recursion.
Require Import GOO.Ordinal.Iteration.
Require Import GOO.Ordinal.VeblenFunction.

Local Open Scope 序数域.

Fixpoint 多元函数 n {T} :=
  match n with
  | O => T
  | S n => 序数 → @多元函数 n T
  end.

Reserved Notation "f '∅..'" (at level 20).
Fixpoint 充零 {n} (f : 多元函数 n) : 序数 :=
  match n, f with
  | O, f => f
  | S m, f => f ∅ ∅..
  end
where "f ∅.." := (充零 f) : 序数域.

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

Definition 极限复合 {n} (F: 序数 → 多元函数 n) (g : nat → 序数) : 多元函数 n :=
  多元极限 (换首元 (λ n, F (g n))).
Notation "F ∘ g" := (极限复合 F g) (format "F ∘ g", at level 9) : 序数域.

Fixpoint veblen {n} (f : 多元函数 (S n)) : 多元函数 (S (S n)) :=
  let fix 增元迭代 (f₁ : 多元函数 1) n : 多元函数 (S n) :=
    match n with
    | O => f₁
    | S m => veblen (增元迭代 f₁ m)
    end in
  (fix inner (f : 多元函数 (S n)) (α : 序数) : 多元函数 (S n) :=
    match α with
    | ∅ => f
    | α⁺ => 增元迭代 (λ β, inner f α β ∅..)′ n
    | lim g => 增元迭代 (递归 (λ β, (inner f)∘g β⁺ ∅..) ((inner f)∘g ∅..)) n
    end
  ) f.

Definition φ n : 多元函数 n :=
  match n with
  | O => ∅
  | S m => let fix inner n : 多元函数 (S n) :=
    match n with
    | O => cantor ∅
    | S m => veblen (inner m)
    end in inner m
  end.

Definition SVO := lim (λ n, φ (S n) [1] ∅..).

Fact φ_0 : φ 0 = ∅.
Proof. reflexivity. Qed.

Fact φ_1 : ∀ α, φ 1 α = cantor ∅ α.
Proof. reflexivity. Qed.

Fact φ_2 : ∀ α β, φ 2 α β = 二元.φ α β.
Proof. reflexivity. Qed.

Fact φ_3 : ∀ α β γ, φ 3 α β γ = 三元.φ α β γ.
Proof. reflexivity. Qed.

Fact φ_4 : ∀ α β γ δ, φ 4 α β γ δ = 四元.φ α β γ δ.
Proof. reflexivity. Qed.
