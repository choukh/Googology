(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.Recursion.
Require Import GOO.Ordinal.Iteration.
Require Import GOO.Ordinal.VeblenFunction.

Local Open Scope 序数域.

Fixpoint 多元函数 n T : Set :=
  match n with
  | O => T
  | S n => 序数 → 多元函数 n T
  end.

Reserved Notation "f '∅..__'" (at level 20).
Fixpoint 充零留二 {n} (f : 多元函数 (S (S n)) 序数) : 多元函数 2 序数 :=
  λ α β, match n, f with
  | O, f => f α β
  | S m, f => f ∅ ∅..__ α β
  end
where "f ∅..__" := (充零留二 f) : 序数域.

Definition 充零留一 {n} (f : 多元函数 (S n) 序数) : 多元函数 1 序数 :=
  match n, f with
  | O, f => f
  | S m, f => f ∅..__ ∅
  end.
Notation "f '∅.._'" := (充零留一 f) (at level 20) : 序数域.

Definition 充零 {n} (f : 多元函数 n 序数) : 序数 :=
  match n, f with
  | O, f => f
  | S m, f => f ∅.._ ∅
  end.
Notation "f '∅..'" := (充零 f) (at level 20) : 序数域.

Fixpoint 换首元 {T : Set} {n} (f : T → 多元函数 n 序数) : 多元函数 n (T → 序数) :=
  match n, f with
  | O, f => f
  | S m, f => λ α, 换首元 (λ n, f n α)
  end.

Fixpoint 多元极限 {n} (f : 多元函数 n (nat → 序数)) : 多元函数 n 序数 :=
  match n, f with
  | O, f => lim f
  | S m, f => λ α, 多元极限 (f α)
  end.

Definition 极限复合 {n} (F: 序数 → 多元函数 n 序数) g : 多元函数 n 序数 :=
  多元极限 (换首元 (λ n, F (g n))).
Notation "F ∘ g" := (极限复合 F g) (format "F ∘ g", at level 9) : 序数域.

(* 增元Helper函数 *)
Fixpoint veblen {n} : 多元函数 (S n) 序数 → 多元函数 (S (S n)) 序数 :=
  let fix 增元迭代 (f₁ : 多元函数 1 序数) n : 多元函数 (S n) 序数 :=
    match n with
    | O => f₁
    | S m => veblen (增元迭代 f₁ m)
    end in
  fix inner (f : 多元函数 (S n) 序数) (α : 序数) : 多元函数 (S n) 序数 :=
    match α with
    | ∅ => f
    | α⁺ => 增元迭代 (λ β, inner f α β ∅..)′ n
    | lim g => 增元迭代 (递归 (λ β, (inner f)∘g β⁺ ∅..) ((inner f)∘g ∅..)) n
    end.

(* n表示从第0到第n的位置上有参数 *)
Fixpoint 广义多元φ f n : 多元函数 (S n) 序数 :=
  match n with
  | O => f
  | S m => veblen (广义多元φ f m)
  end.

Definition φ := 广义多元φ (cantor ∅).

Definition SVO := lim (λ n, φ n [1] ∅..).

Fact φ_0 : φ 0 = cantor ∅.
Proof. reflexivity. Qed.

Fact φ_1 : φ 1 = 二元.φ.
Proof. reflexivity. Qed.

Fact φ_2 : φ 2 = 三元.φ.
Proof. reflexivity. Qed.

Fact φ_3 : φ 3 = 四元.φ.
Proof. reflexivity. Qed.

(** x表示单个任意参数, s表示后继, z表示零, 大写表示不定多个 **)

Lemma φ_z_X : ∀ n, φ (S n) ∅ = φ n.
Proof. destruct n; reflexivity. Qed.

Lemma φ_s_Z_x : ∀ n α x, φ (S n) α⁺ ∅.._ x = (λ β, φ (S n) α β ∅..)′ x.
Proof.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
Admitted.

Fact φ_x_Z_s : ∀ n α β, φ (S (S n)) α ∅..__ β⁺ = (φ (S (S n)) α ∅..__ β)′.
Proof.
  destruct n. destruct α; reflexivity.
  destruct n. destruct α; reflexivity.
  destruct n. destruct α; reflexivity.
Admitted.
