(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.Recursion.
Require Import GOO.Ordinal.Iteration.
Require Import GOO.Ordinal.VeblenFunction.

Local Open Scope 序数域.

Fixpoint 多元 n T : Set :=
  match n with
  | O => T
  | S n => 序数 → 多元 n T
  end.

Reserved Notation "F '∅..'" (at level 20).
Fixpoint 充零 {n} {T} (F : 多元 n T) : T :=
  match n, F with
  | O, F => F
  | S m, F => F ∅ ∅..
  end
where "F ∅.." := (充零 F) : 序数域.

Reserved Notation "F '∅.._'" (at level 20).
Fixpoint 充零留一 {n} {T} (F : 多元 (S n) T) : 多元 1 T :=
  match n, F with
  | O, F => F
  | S m, F => F ∅ ∅.._
  end
where "F ∅.._" := (充零留一 F) : 序数域.

Reserved Notation "f '∅..__'" (at level 20).
Fixpoint 充零留二 {n} {T} (F : 多元 (S (S n)) T) : 多元 2 T :=
  match n, F with
  | O, F => F
  | S m, F => F ∅ ∅..__
  end
where "F ∅..__" := (充零留二 F) : 序数域.

(* 步进增元函数 *)
Fixpoint veblen {n} : 多元 (S n) 序数 → 多元 (S (S n)) 序数 :=
  let fix 增元迭代 (F : 多元 1 序数) n : 多元 (S n) 序数 :=
    match n with
    | O => F
    | S m => veblen (增元迭代 F m)
    end in
  fix inner (F : 多元 (S n) 序数) (α : 序数) : 多元 (S n) 序数 :=
    match α with
    | ∅ => F
    | α⁺ => 增元迭代 (λ β, inner F α β ∅..)′ n
    | lim f =>
      let G₀ := lim (λ m, inner F (f m) ∅..) in
      let G := λ β, lim (λ m, inner F (f m) β⁺ ∅..) in
      增元迭代 (递归 G G₀) n
    end.

(* 此即veblen函数的内联递归, 受停机检查器限制, 它无法先于veblen定义 *)
(* n表示从第0到第n的位置上有参数 *)
Fixpoint 增元迭代 F n : 多元 (S n) 序数 :=
  match n with
  | O => F
  | S m => veblen (增元迭代 F m)
  end.

Definition φ := 增元迭代 (cantor ∅).

Definition SVO := lim (λ n, φ n [1] ∅..).

Fact φ_0 : φ 0 = cantor ∅.
Proof. reflexivity. Qed.

Fact φ_1 : φ 1 = 二元.φ.
Proof. reflexivity. Qed.

Fact φ_2 : φ 2 = 三元.φ.
Proof. reflexivity. Qed.

Fact φ_3 : φ 3 = 四元.φ.
Proof. reflexivity. Qed.

(** x,y表示单个任意参数, z表示零, s表示后继, l表示极限, 大写表示不定多个 **)

Lemma f_Z_eq_f_Z_z : ∀ n T (F : 多元 (S n) T), F ∅.. = F ∅.._ ∅.
Proof. intros. induction n. reflexivity. simpl. rewrite <- IHn. reflexivity. Qed.

Lemma f_Z_eq_f_z_Z : ∀ n T (F : 多元 (S n) T), F ∅.. = F ∅ ∅...
Proof. intros. induction n. reflexivity. simpl. rewrite <- IHn. reflexivity. Qed.

Lemma veblen_z : ∀ n (F : 多元 (S n) 序数), veblen F ∅ = F.
Proof. destruct n; reflexivity. Qed.

Lemma 增元迭代_Z_x : ∀ F n, (增元迭代 F n) ∅.._ = F.
Proof.
  intros. induction n. reflexivity.
  simpl. rewrite veblen_z, IHn. reflexivity.
Qed.

Lemma veblen_s_Z_x : ∀ n (F : 多元 (S n) 序数) α,
  veblen F α⁺ ∅.._ = (λ β, veblen F α β ∅..)′.
Proof.
  intros. destruct n. reflexivity.
  simpl. rewrite veblen_z. rewrite 增元迭代_Z_x. reflexivity.
Qed.

Lemma veblen_l_Z_x : ∀ n (F : 多元 (S n) 序数) f, veblen F (lim f) ∅.._ =
  递归 (λ ξ, lim (λ m, veblen F (f m) ξ⁺ ∅..)) (lim (λ m, veblen F (f m) ∅ ∅..)).
Proof.
  intros. destruct n. reflexivity.
  simpl. rewrite veblen_z. rewrite 增元迭代_Z_x. reflexivity.
Qed.

Lemma 增元迭代_x_s_Z_y : ∀ n F α β, 增元迭代 F (S (S n)) α β⁺ ∅.._ =
  (λ γ, 增元迭代 F (S (S n)) α β γ ∅..)′.
Proof.
  intros. destruct α.
  - simpl. rewrite veblen_s_Z_x. reflexivity.
  - unfold 增元迭代. simpl. rewrite veblen_s_Z_x. reflexivity.
  - unfold 增元迭代. simpl. rewrite veblen_s_Z_x. reflexivity.
Qed.

Lemma 增元迭代_x_l_Z_y : ∀ n F α f, 增元迭代 F (S (S n)) α (lim f) ∅.._ =
  递归 (λ ξ, lim (λ m, 增元迭代 F (S (S n)) α (f m) ξ⁺ ∅..)) (lim (λ m, 增元迭代 F (S (S n)) α (f m) ∅ ∅..)).
Proof.
  intros. destruct α.
  - simpl. rewrite veblen_l_Z_x. reflexivity.
  - unfold 增元迭代. simpl. rewrite veblen_l_Z_x. reflexivity.
  - unfold 增元迭代. simpl. rewrite veblen_l_Z_x. reflexivity.
Qed.

Lemma 增元迭代_Z_s_x : ∀ F n α, veblen (增元迭代 F n) ∅..__ α⁺ = (veblen (增元迭代 F n) ∅..__ α)′.
Proof.
  intros. induction n. reflexivity.
  simpl in *. rewrite IHn. reflexivity.
Qed.

Lemma veblen_s_Z_s_x : ∀ n (F : 多元 (S (S n)) 序数) α β,
  veblen F α⁺ ∅..__ β⁺ = (veblen F α⁺ ∅..__ β)′.
Proof. intros. simpl. rewrite 增元迭代_Z_s_x. reflexivity. Qed.

Lemma veblen_l_Z_s_x : ∀ n (F : 多元 (S (S n)) 序数) f β,
  veblen F (lim f) ∅..__ β⁺ = (veblen F (lim f) ∅..__ β)′.
Proof. intros. simpl. rewrite 增元迭代_Z_s_x. reflexivity. Qed.

Lemma 增元迭代_x_Z_s_y : ∀ n F α β,
  (增元迭代 F (S (S n))) α ∅..__ β⁺ = ((增元迭代 F (S (S n))) α ∅..__ β)′.
Proof.
  intros. destruct α.
  - induction n. reflexivity. simpl in *. rewrite IHn. reflexivity.
  - unfold 增元迭代. rewrite veblen_s_Z_s_x. reflexivity.
  - unfold 增元迭代. rewrite veblen_l_Z_s_x. reflexivity.
Qed.

Lemma 增元迭代_Z_l_x : ∀ F n f, veblen (增元迭代 F n) ∅..__ (lim f) =
  递归 (λ ξ, lim (λ m, veblen (增元迭代 F n) ∅..__ (f m) ξ⁺)) (lim (λ m, veblen (增元迭代 F n) ∅..__ (f m) ∅)).
Proof.
  intros. induction n. reflexivity.
  simpl in *. rewrite IHn. reflexivity.
Qed.

Lemma veblen_s_Z_l_x : ∀ n (F : 多元 (S (S n)) 序数) α f, veblen F α⁺ ∅..__ (lim f) =
  递归 (λ ξ, lim (λ m, veblen F α⁺ ∅..__ (f m) ξ⁺)) (lim (λ m, veblen F α⁺ ∅..__ (f m) ∅)).
Proof. intros. simpl. rewrite 增元迭代_Z_l_x. reflexivity. Qed.

Lemma veblen_l_Z_l_x : ∀ n (F : 多元 (S (S n)) 序数) f g, veblen F (lim f) ∅..__ (lim g) =
  递归 (λ ξ, lim (λ m, veblen F (lim f) ∅..__ (g m) ξ⁺)) (lim (λ m, veblen F (lim f) ∅..__ (g m) ∅)).
Proof. intros. simpl. rewrite 增元迭代_Z_l_x. reflexivity. Qed.

Lemma 增元迭代_x_Z_l_y : ∀ n F α f, (增元迭代 F (S (S n))) α ∅..__ (lim f) =
  递归 (λ ξ, lim (λ m, (增元迭代 F (S (S n))) α ∅..__ (f m) ξ⁺)) (lim (λ m, (增元迭代 F (S (S n))) α ∅..__ (f m) ∅)).
Proof.
  intros. destruct α.
  - induction n. reflexivity. simpl in *. rewrite IHn. reflexivity.
  - unfold 增元迭代. rewrite veblen_s_Z_l_x. reflexivity.
  - unfold 增元迭代. rewrite veblen_l_Z_l_x. reflexivity.
Qed.

Theorem φ_z_X : ∀ n, φ (S n) ∅ = φ n.
Proof. destruct n; reflexivity. Qed.

Theorem φ_s_Z_x : ∀ n α, φ (S n) α⁺ ∅.._ = (λ β, φ (S n) α β ∅..)′.
Proof. intros. unfold φ, 增元迭代. rewrite veblen_s_Z_x. reflexivity. Qed.

Theorem φ_l_Z_x : ∀ n f, φ (S n) (lim f) ∅.._ =
  递归 (λ ξ, lim (λ m, φ (S n) (f m) ξ⁺ ∅..)) (lim (λ m, φ (S n) (f m) ∅ ∅..)).
Proof. intros. unfold φ, 增元迭代. rewrite veblen_l_Z_x. reflexivity. Qed.

Corollary φ_l_Z_z : ∀ n f, φ n (lim f) ∅.. = lim (λ m, φ n (f m) ∅..).
Proof. intros. destruct n. reflexivity. rewrite f_Z_eq_f_Z_z, φ_l_Z_x. reflexivity. Qed.

Corollary φ_l_Z_s : ∀ n f α, φ (S n) (lim f) ∅.._ α⁺ =
  lim (λ m, φ (S n) (f m) (φ (S n) (lim f) ∅.._ α)⁺ ∅..).
Proof. intros. rewrite φ_l_Z_x. reflexivity. Qed.

Corollary φ_l_Z_l : ∀ n f g, φ (S n) (lim f) ∅.._ (lim g) =
  lim (λ m, φ (S n) (lim f) ∅.._ (g m)).
Proof. intros. rewrite φ_l_Z_x. reflexivity. Qed.

Theorem φ_x_s_Z_y : ∀ n α β, φ (S (S n)) α β⁺ ∅.._ = (λ γ, φ (S (S n)) α β γ ∅..)′.
Proof. intros. unfold φ. rewrite 增元迭代_x_s_Z_y. reflexivity. Qed.

Theorem φ_x_l_Z_y : ∀ n α f, φ (S (S n)) α (lim f) ∅.._ =
  递归 (λ ξ, lim (λ m, φ (S (S n)) α (f m) ξ⁺ ∅..)) (lim (λ m, φ (S (S n)) α (f m) ∅ ∅..)).
Proof. intros. unfold φ. rewrite 增元迭代_x_l_Z_y. reflexivity. Qed.

Theorem φ_x_Z_s_y : ∀ n α β, φ (S (S n)) α ∅..__ β⁺ = (φ (S (S n)) α ∅..__ β)′.
Proof. intros. unfold φ. rewrite 增元迭代_x_Z_s_y. reflexivity. Qed.

Theorem φ_x_Z_l_y : ∀ n α f, φ (S (S n)) α ∅..__ (lim f) =
  递归 (λ ξ, lim (λ m, φ (S (S n)) α ∅..__ (f m) ξ⁺)) (lim (λ m, φ (S (S n)) α ∅..__ (f m) ∅)).
Proof. intros. unfold φ. rewrite 增元迭代_x_Z_l_y. reflexivity. Qed.

Corollary φ_x_l_Z_z : ∀ n α f, φ (S n) α (lim f) ∅.. = lim (λ m, φ (S n) α (f m) ∅..).
Proof. intros. destruct n. destruct α; reflexivity. rewrite f_Z_eq_f_Z_z, φ_x_l_Z_y. reflexivity. Qed.

Corollary φ_x_l_Z_s : ∀ n α f β, φ (S (S n)) α (lim f) ∅.._ β⁺ =
  lim (λ m, φ (S (S n)) α (f m) (φ (S (S n)) α (lim f) ∅.._ β)⁺ ∅..).
Proof. intros. destruct α; rewrite φ_x_l_Z_y; reflexivity. Qed.

Corollary φ_x_l_Z_l : ∀ n α f g, φ (S (S n)) α (lim f) ∅.._ (lim g) =
  lim (λ m, φ (S (S n)) α (lim f) ∅.._ (g m)).
Proof. intros. destruct α; rewrite φ_x_l_Z_y; reflexivity. Qed.

Corollary φ_x_Z_l_z : ∀ n α f, φ (S (S n)) α ∅..__ (lim f) ∅ = lim (λ m, φ (S (S n)) α ∅..__ (f m) ∅).
Proof. intros. rewrite φ_x_Z_l_y. reflexivity. Qed.

Corollary φ_x_Z_l_s : ∀ n α f β, φ (S (S n)) α ∅..__ (lim f) β⁺ =
  lim (λ m, φ (S (S n)) α ∅..__ (f m) (φ (S (S n)) α ∅..__ (lim f) β)⁺).
Proof. intros. destruct α; rewrite φ_x_Z_l_y; reflexivity. Qed.

Corollary φ_x_Z_l_l : ∀ n α f g, φ (S (S n)) α ∅..__ (lim f) (lim g) =
  lim (λ m, φ (S (S n)) α ∅..__ (lim f) (g m)).
Proof. intros. destruct α; rewrite φ_x_Z_l_y; reflexivity. Qed.
