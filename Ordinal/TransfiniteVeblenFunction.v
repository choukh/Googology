(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.Recursion.
Require Import GOO.Ordinal.Iteration.
Require Import GOO.Ordinal.VeblenFunction.
Require Import GOO.Ordinal.ExtendedVeblenFunction.

Local Open Scope 序数域.

Notation ω元φ := ExtendedVeblenFunction.φ.
Notation ω元函数 := (∀ n, 多元函数 (S n) 序数).
Definition ω多元函数 n := 多元函数 (S n) (ω元函数).

Module ω加一元.

Fixpoint veblen (f : ω元函数) α n : 多元函数 (S n) 序数 := match α with
  | ∅ => f n
  | α⁺ =>
    let h₀ := lim (λ n, veblen f α n [1] ∅..) in
    let h := λ β, lim (λ n, veblen f α n β⁺ ∅..) in
    增元迭代 (递归 h h₀) n
  | lim g =>
    let h₀ := lim (λ n, veblen f (g n) 0 ∅) in
    let h := λ β, lim (λ n, veblen f (g n) 0 β⁺) in
    增元迭代 (递归 h h₀) n
  end.

Definition φ := veblen ω元φ.

Fact φ_z_X : ∀ n, φ ∅ n = ω元φ n.
Proof. reflexivity. Qed.

Theorem φ_x_n_Z : ∀ α n, φ α n ∅.. = φ α 0 ∅.
Proof.
  intros. destruct α.
  - induction n. reflexivity. rewrite φ_z_X in *. simpl.
    rewrite ExtendedVeblenFunction.φ_z_X, <- f_Z_eq_f_z_Z, IHn. reflexivity.
  - unfold φ, veblen. rewrite f_Z_eq_f_Z_z, 增元迭代_Z_x. reflexivity.
  - unfold φ, veblen. rewrite f_Z_eq_f_Z_z, 增元迭代_Z_x. reflexivity.
Qed.

Fact φ_1_Z : φ [1] 0 ∅ = SVO.
Proof. reflexivity. Qed.

Fact φ_s_Z : ∀ α, φ α⁺ 0 ∅ = lim (λ n, φ α n [1] ∅..).
Proof. reflexivity. Qed.

Fact φ_1_Z_1 : φ [1] 0 [1] = lim (λ n, ω元φ n SVO⁺ ∅..).
Proof. reflexivity. Qed.

Fact φ_s_Z_1 : ∀ α, φ α⁺ 0 [1] = lim (λ n, φ α n (φ α⁺ 0 ∅)⁺ ∅..).
Proof. reflexivity. Qed.

Fact φ_s_Z_s : ∀ α β, φ α⁺ 0 β⁺ = lim (λ n, φ α n (φ α⁺ 0 β)⁺ ∅..).
Proof. reflexivity. Qed.

Fact φ_s_Z_l : ∀ α f, φ α⁺ 0 (lim f) = lim (λ n, φ α⁺ 0 (f n)).
Proof. reflexivity. Qed.

Fact φ_s_Z_1_z : ∀ α, φ α⁺ 1 [1] ∅ = Itω (φ α⁺ 0) ∅.
Proof. reflexivity. Qed.

Fact φ_s_Z_1_x : ∀ α, φ α⁺ 1 [1] = (φ α⁺ 0)′.
Proof. reflexivity. Qed.

Fact φ_x_Z_s_y : ∀ α β, φ α⁺ 1 β⁺ = (φ α⁺ 1 β)′.
Proof. reflexivity. Qed.

Fact φ_x_Z_l_z : ∀ α f, φ α⁺ 1 (lim f) ∅ = lim (λ n, φ α⁺ 1 (f n) ∅).
Proof. reflexivity. Qed.

Fact φ_x_Z_l_s : ∀ α f β, φ α⁺ 1 (lim f) β⁺ = lim (λ n, φ α⁺ 1 (f n) (φ α⁺ 1 (lim f) β)⁺).
Proof. reflexivity. Qed.

Fact φ_x_Z_l_l : ∀ α f g, φ α⁺ 1 (lim f) (lim g) = lim (λ n, φ α⁺ 1 (lim f) (g n)).
Proof. reflexivity. Qed.

Fact φ_l_Z : ∀ f, φ (lim f) 0 ∅ = lim (λ n, φ (f n) 0 ∅).
Proof. reflexivity. Qed.

Fact φ_l_Z_1 : ∀ f, φ (lim f) 0 [1] = lim (λ n, φ (f n) 0 (φ (lim f) 0 ∅)⁺).
Proof. reflexivity. Qed.

Fact φ_l_Z_s : ∀ f α, φ (lim f) 0 α⁺ = lim (λ n, φ (f n) 0 (φ (lim f) 0 α)⁺).
Proof. reflexivity. Qed.

Fact φ_l_Z_l : ∀ f g, φ (lim f) 0 (lim g) = lim (λ n, φ (lim f) 0 (g n)).
Proof. reflexivity. Qed.

Fact φ_l_Z_1_0 : ∀ f, φ (lim f) 1 [1] ∅ = Itω (φ (lim f) 0) ∅.
Proof. reflexivity. Qed.

Fact φ_l_Z_1_x : ∀ f, φ (lim f) 1 [1] = (φ (lim f) 0)′.
Proof. reflexivity. Qed.

Fact φ_l_Z_s_x : ∀ f α, φ (lim f) 1 α⁺ = (φ (lim f) 1 α)′.
Proof. reflexivity. Qed.

Fact φ_l_Z_l_z : ∀ f g, φ (lim f) 1 (lim g) ∅ = lim (λ n, φ (lim f) 1 (g n) ∅).
Proof. reflexivity. Qed.

Fact φ_l_Z_l_s : ∀ f g α, φ (lim f) 1 (lim g) α⁺ = lim (λ n, φ (lim f) 1 (g n) (φ (lim f) 1 (lim g) α)⁺).
Proof. reflexivity. Qed.

Fact φ_l_Z_l_l : ∀ f g h, φ (lim f) 1 (lim g) (lim h) = lim (λ n, φ (lim f) 1 (lim g) (h n)).
Proof. reflexivity. Qed.

Theorem φ_s_Z_s_Z_x : ∀ α n β x, φ α⁺ (S n) β⁺ ∅.._ x = (λ ξ, φ α⁺ (S n) β ξ ∅..)′ x.
Proof. intros. unfold φ, veblen, 增元迭代. rewrite veblen_s_Z_x. reflexivity. Qed.

Theorem φ_s_Z_l_Z_x : ∀ α n f, φ α⁺ (S n) (lim f) ∅.._ =
  递归 (λ ξ, lim (λ m, φ α⁺ (S n) (f m) ξ⁺ ∅..)) (lim (λ m, φ α⁺ (S n) (f m) ∅ ∅..)).
Proof. intros. unfold φ, veblen, 增元迭代. rewrite veblen_l_Z_x. reflexivity. Qed.

Corollary φ_s_Z_l_Z_z : ∀ α n f, φ α⁺ n (lim f) ∅.. = lim (λ m, φ α⁺ n (f m) ∅..).
Proof. intros. destruct n. reflexivity. rewrite f_Z_eq_f_Z_z, φ_s_Z_l_Z_x. reflexivity. Qed.

Corollary φ_s_Z_l_Z_s : ∀ α n f β, φ α⁺ (S n) (lim f) ∅.._ β⁺ =
  lim (λ m, φ α⁺ (S n) (f m) (φ α⁺ (S n) (lim f) ∅.._ β)⁺ ∅..).
Proof. intros. rewrite φ_s_Z_l_Z_x. reflexivity. Qed.

Corollary φ_s_Z_l_Z_l : ∀ α n f g, φ α⁺ (S n) (lim f) ∅.._ (lim g) =
  lim (λ m, φ α⁺ (S n) (lim f) ∅.._ (g m)).
Proof. intros. rewrite φ_s_Z_l_Z_x. reflexivity. Qed.

Theorem φ_l_Z_s_Z_x : ∀ f n α x, φ (lim f) (S n) α⁺ ∅.._ x = (λ ξ, φ (lim f) (S n) α ξ ∅..)′ x.
Proof. intros. unfold φ, veblen, 增元迭代. rewrite veblen_s_Z_x. reflexivity. Qed.

Theorem φ_l_Z_l_Z_x : ∀ f n g, φ (lim f) (S n) (lim g) ∅.._ =
  递归 (λ ξ, lim (λ m, φ (lim f) (S n) (g m) ξ⁺ ∅..)) (lim (λ m, φ (lim f) (S n) (g m) ∅ ∅..)).
Proof. intros. unfold φ, veblen, 增元迭代. rewrite veblen_l_Z_x. reflexivity. Qed.

Corollary φ_l_Z_l_Z_z : ∀ f n g, φ (lim f) n (lim g) ∅.. = lim (λ m, φ (lim f) n (g m) ∅..).
Proof. intros. destruct n. reflexivity. rewrite f_Z_eq_f_Z_z, φ_l_Z_l_Z_x. reflexivity. Qed.

Corollary φ_l_Z_l_Z_s : ∀ f n g α, φ (lim f) (S n) (lim g) ∅.._ α⁺ =
  lim (λ m, φ (lim f) (S n) (g m) (φ (lim f) (S n) (lim g) ∅.._ α)⁺ ∅..).
Proof. intros. rewrite φ_l_Z_l_Z_x. reflexivity. Qed.

Corollary φ_l_Z_l_Z_l : ∀ f n g h, φ (lim f) (S n) (lim g) ∅.._ (lim h) =
  lim (λ m, φ (lim f) (S n) (lim g) ∅.._ (h m)).
Proof. intros. rewrite φ_l_Z_l_Z_x. reflexivity. Qed.

Example φ_sω_Z : φ ω⁺ 0 ∅ = lim (λ n, φ ω n [1] ∅..).
Proof. reflexivity. Qed.

Example φ_φωZ_Z : φ (φ [1] 0 ∅) 0 ∅ = lim (λ n, φ (ω元φ n [1] ∅..) 0 ∅).
Proof. reflexivity. Qed.

End ω加一元.

Module ω加二元.

Fixpoint veblen (f : 序数 → ω元函数) (α : 序数) : 序数 → ω元函数.
  destruct α as [| |g].
  - apply f.
  - intros β n. simpl.
    set (增元迭代 (λ β, veblen f α β 0 ∅)′) as ω元.
    apply (ω加一元.veblen ω元 β).
  - intros β n. simpl.
    set (lim (λ m, veblen f (g m) ∅ 0 ∅)) as h₀.
    set (λ β, lim (λ m, veblen f (g m) β⁺ 0 ∅)) as h.
    set (增元迭代 (递归 h h₀)) as ω元.
    apply (ω加一元.veblen ω元 β).
Defined.

Definition φ := veblen (ω加一元.φ).

Fact φ_z_X : φ ∅ = ω加一元.φ.
Proof. reflexivity. Qed.

Fact φ_1_Z : φ [1] ∅ 0 ∅ = Itω (λ ξ, φ ∅ ξ 0 ∅) ∅.
Proof. reflexivity. Qed.

Fact φ_1_Z_x : φ [1] ∅ 0 = (λ β, φ ∅ β 0 ∅)′.
Proof. reflexivity. Qed.

Fact φ_s_Z_x : ∀ α, φ α⁺ ∅ 0 = (λ β, φ α β 0 ∅)′.
Proof. reflexivity. Qed.

Fact φ_l_Z_x : ∀ f, φ (lim f) ∅ 0 =
  递归 (λ ξ, lim (λ m, φ (f m) ξ⁺ 0 ∅)) (lim (λ m, φ (f m) ∅ 0 ∅)).
Proof. reflexivity. Qed.

Fact φ_x_s_Z : ∀ α β, φ α β⁺ 0 ∅ = lim (λ n, φ α β n [1] ∅..).
Proof. destruct α; reflexivity. Qed.

Fact φ_x_s_Z_s : ∀ α β γ, φ α β⁺ 0 γ⁺ = lim (λ n, φ α β n (φ α β⁺ 0 γ)⁺ ∅..).
Proof. destruct α; reflexivity. Qed.

Fact φ_x_s_Z_l : ∀ α β f, φ α β⁺ 0 (lim f) = lim (λ n, φ α β⁺ 0 (f n)).
Proof. destruct α; reflexivity. Qed.

Fact φ_x_l_Z : ∀ α f, φ α (lim f) 0 ∅ = lim (λ n, φ α (f n) 0 ∅).
Proof. destruct α; reflexivity. Qed.

Fact φ_x_l_Z_1 : ∀ α f, φ α (lim f) 0 [1] = lim (λ n, φ α (f n) 0 (φ α (lim f) 0 ∅)⁺).
Proof. destruct α; reflexivity. Qed.

Fact φ_x_l_Z_s : ∀ α f β, φ α (lim f) 0 β⁺ = lim (λ n, φ α (f n) 0 (φ α (lim f) 0 β)⁺).
Proof. destruct α; reflexivity. Qed.

End ω加二元.
