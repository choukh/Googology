(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.Recursion.
Require Import GOO.Ordinal.Iteration.
Require Import GOO.Ordinal.VeblenFunction.
Require Import GOO.Ordinal.ExtendedVeblenFunction.

Local Open Scope 序数域.

Notation ω元φ := ExtendedVeblenFunction.φ.
Notation ω增元迭代 := ExtendedVeblenFunction.增元迭代.

Notation ω元 := (∀ n, 多元 (S n) 序数).
Notation ω后继元 n := (多元 n (ω元)).
Notation ω2元 := (∀ n, ω后继元 (S n)).

Module ω加一元.

Fixpoint 跳出 (F : ω元) α n : 多元 (S n) 序数 := match α with
  | ∅ => F n
  | α⁺ =>
    let G₀ := lim (λ n, 跳出 F α n [1] ∅..) in
    let G := λ β, lim (λ n, 跳出 F α n β⁺ ∅..) in
    ω增元迭代 (递归 G G₀) n
  | lim f =>
    let G₀ := lim (λ n, 跳出 F (f n) 0 ∅) in
    let G := λ β, lim (λ n, 跳出 F (f n) 0 β⁺) in
    ω增元迭代 (递归 G G₀) n
  end.

Definition φ := 跳出 ω元φ.

Fact φ_z_X : ∀ n, φ ∅ n = ω元φ n.
Proof. reflexivity. Qed.

Theorem φ_x_n_Z : ∀ α n, φ α n ∅.. = φ α 0 ∅.
Proof.
  intros. destruct α.
  - induction n. reflexivity. rewrite φ_z_X in *. simpl.
    rewrite ExtendedVeblenFunction.φ_z_X, <- f_Z_eq_f_z_Z, IHn. reflexivity.
  - unfold φ, 跳出. rewrite f_Z_eq_f_Z_z, 增元迭代_Z_x. reflexivity.
  - unfold φ, 跳出. rewrite f_Z_eq_f_Z_z, 增元迭代_Z_x. reflexivity.
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
Proof. intros. unfold φ, 跳出, 增元迭代. rewrite veblen_s_Z_x. reflexivity. Qed.

Theorem φ_s_Z_l_Z_x : ∀ α n f, φ α⁺ (S n) (lim f) ∅.._ =
  递归 (λ ξ, lim (λ m, φ α⁺ (S n) (f m) ξ⁺ ∅..)) (lim (λ m, φ α⁺ (S n) (f m) ∅ ∅..)).
Proof. intros. unfold φ, 跳出, 增元迭代. rewrite veblen_l_Z_x. reflexivity. Qed.

Corollary φ_s_Z_l_Z_z : ∀ α n f, φ α⁺ n (lim f) ∅.. = lim (λ m, φ α⁺ n (f m) ∅..).
Proof. intros. destruct n. reflexivity. rewrite f_Z_eq_f_Z_z, φ_s_Z_l_Z_x. reflexivity. Qed.

Corollary φ_s_Z_l_Z_s : ∀ α n f β, φ α⁺ (S n) (lim f) ∅.._ β⁺ =
  lim (λ m, φ α⁺ (S n) (f m) (φ α⁺ (S n) (lim f) ∅.._ β)⁺ ∅..).
Proof. intros. rewrite φ_s_Z_l_Z_x. reflexivity. Qed.

Corollary φ_s_Z_l_Z_l : ∀ α n f g, φ α⁺ (S n) (lim f) ∅.._ (lim g) =
  lim (λ m, φ α⁺ (S n) (lim f) ∅.._ (g m)).
Proof. intros. rewrite φ_s_Z_l_Z_x. reflexivity. Qed.

Theorem φ_l_Z_s_Z_x : ∀ f n α x, φ (lim f) (S n) α⁺ ∅.._ x = (λ ξ, φ (lim f) (S n) α ξ ∅..)′ x.
Proof. intros. unfold φ, 跳出, 增元迭代. rewrite veblen_s_Z_x. reflexivity. Qed.

Theorem φ_l_Z_l_Z_x : ∀ f n g, φ (lim f) (S n) (lim g) ∅.._ =
  递归 (λ ξ, lim (λ m, φ (lim f) (S n) (g m) ξ⁺ ∅..)) (lim (λ m, φ (lim f) (S n) (g m) ∅ ∅..)).
Proof. intros. unfold φ, 跳出, 增元迭代. rewrite veblen_l_Z_x. reflexivity. Qed.

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

Fixpoint veblen (F : 序数 → ω元) (α : 序数) : 序数 → ω元.
  destruct α as [|α|f].
  - apply F.
  - set (增元迭代 (λ β, veblen F α β 0 ∅)′) as ω元F.
    apply (ω加一元.跳出 ω元F).
  - set (lim (λ m, veblen F (f m) ∅ 0 ∅)) as G₀.
    set (λ β, lim (λ m, veblen F (f m) β⁺ 0 ∅)) as G.
    set (增元迭代 (递归 G G₀)) as ω元F.
    apply (ω加一元.跳出 ω元F).
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

Module ω2元.

Fixpoint veblen {n} : ω后继元 (S n) → ω后继元 (S (S n)).
  set (fix 增元迭代 (F : ω后继元 1) n : ω后继元 (S n) :=
    match n with
    | O => F
    | S m => veblen m (增元迭代 F m)
    end) as 增元迭代.
  refine (fix inner (F : ω后继元 (S n)) (α : 序数) : ω后继元 (S n) := _).
  destruct α as [|α|g].
  - apply F.
  - set (ω增元迭代 (λ β, inner F α β ∅.. 0 ∅)′) as ω元F.
    apply (增元迭代 (ω加一元.跳出 ω元F) n).
  - set (lim (λ m, inner F (g m) ∅.. 0 ∅)) as G₀.
    set (λ β, lim (λ m, inner F (g m) β⁺ ∅.. 0 ∅)) as G.
    set (ω增元迭代 (递归 G G₀)) as ω元F.
    apply (增元迭代 (ω加一元.跳出 ω元F) n).
Defined.

Fixpoint 增元迭代 F n : ω后继元 (S n) :=
  match n with
    | O => F
    | S m => veblen (增元迭代 F m)
  end.

Definition φ := 增元迭代 (ω加一元.φ).

Lemma veblen_z : ∀ n (F : ω后继元 (S n)), veblen F ∅ = F.
Proof. destruct n; reflexivity. Qed.

Lemma 增元迭代_Z_x__X : ∀ F n, (增元迭代 F n) ∅.._ = F.
Proof.
  intros. induction n. reflexivity.
  simpl. rewrite veblen_z. easy.
Qed.

Lemma veblen_s_Z_x : ∀ n (F : ω后继元 (S n)) α,
  veblen F α⁺ ∅ ∅.. 0 = (λ β, veblen F α β ∅.. 0 ∅)′.
Proof.
  intros. destruct n. reflexivity.
  simpl. rewrite veblen_z, <- f_Z_eq_f_z_Z, f_Z_eq_f_Z_z.
  rewrite 增元迭代_Z_x__X. reflexivity.
Qed.

Lemma veblen_l_Z_x : ∀ n (F : ω后继元 (S n)) f, veblen F (lim f) ∅ ∅.. 0 =
  递归 (λ ξ, lim (λ m, veblen F (f m) ξ⁺ ∅.. 0 ∅)) (lim (λ m, veblen F (f m) ∅ ∅.. 0 ∅)).
Proof.
  intros. destruct n. reflexivity.
  simpl. rewrite veblen_z, <- f_Z_eq_f_z_Z, f_Z_eq_f_Z_z.
  rewrite 增元迭代_Z_x__X. reflexivity.
Qed.

Lemma 增元迭代_x_s_Z_y : ∀ n F α β, 增元迭代 F (S (S n)) α β⁺ ∅ ∅.. 0 =
  (λ γ, 增元迭代 F (S (S n)) α β γ ∅.. 0 ∅)′.
Proof.
  intros. destruct α.
  - simpl. rewrite veblen_s_Z_x. reflexivity.
  - unfold 增元迭代. simpl. rewrite veblen_s_Z_x. reflexivity.
  - unfold 增元迭代. simpl. rewrite veblen_s_Z_x. reflexivity.
Qed.

Lemma 增元迭代_x_l_Z_y : ∀ n F α f, 增元迭代 F (S (S n)) α (lim f) ∅ ∅.. 0 =
  递归 (λ ξ, lim (λ m, 增元迭代 F (S (S n)) α (f m) ξ⁺ ∅.. 0 ∅)) (lim (λ m, 增元迭代 F (S (S n)) α (f m) ∅ ∅.. 0 ∅)).
Proof.
  intros. destruct α.
  - simpl. rewrite veblen_l_Z_x. reflexivity.
  - unfold 增元迭代. simpl. rewrite veblen_l_Z_x. reflexivity.
  - unfold 增元迭代. simpl. rewrite veblen_l_Z_x. reflexivity.
Qed.

Lemma 增元迭代_Z__Z_s_x : ∀ F n α,
  veblen (增元迭代 (ω加一元.跳出 (ω增元迭代 F)) n) ∅.. 1 α⁺ =
  (veblen (增元迭代 (ω加一元.跳出 (ω增元迭代 F)) n) ∅.. 1 α)′.
Proof.
  intros. induction n. reflexivity.
  simpl in *. rewrite IHn. reflexivity.
Qed.

Lemma veblen_s_Z__Z_s_x : ∀ n (F : ω后继元 (S n)) α β,
  veblen F α⁺ ∅ ∅.. 1 β⁺ = (veblen F α⁺ ∅ ∅.. 1 β)′.
Proof.
  intros. destruct n. reflexivity. simpl.
  rewrite <- f_Z_eq_f_z_Z, <- f_Z_eq_f_z_Z, 增元迭代_Z__Z_s_x. reflexivity.
Qed.

Lemma veblen_l_Z__Z_s_x : ∀ n (F : ω后继元 (S n)) f α,
  veblen F (lim f) ∅ ∅.. 1 α⁺ = (veblen F (lim f) ∅ ∅.. 1 α)′.
Proof.
  intros. destruct n. reflexivity. simpl.
  rewrite <- f_Z_eq_f_z_Z, <- f_Z_eq_f_z_Z, 增元迭代_Z__Z_s_x. reflexivity.
Qed.

Lemma 增元迭代_x_Z__Z_s_y : ∀ n α β,
  增元迭代 (ω加一元.φ) n α ∅.. 1 β⁺ = (增元迭代 (ω加一元.φ) n α ∅.. 1 β)′.
Proof.
  intros. destruct α.
  - induction n. reflexivity. simpl. rewrite veblen_z. apply IHn.
  - unfold 增元迭代. destruct n. reflexivity.
    rewrite f_Z_eq_f_z_Z, veblen_s_Z__Z_s_x. reflexivity.
  - unfold 增元迭代. destruct n. reflexivity.
    rewrite f_Z_eq_f_z_Z, veblen_l_Z__Z_s_x. reflexivity.
Qed.

Lemma 增元迭代_Z__Z_l_x : ∀ F n f,
  let G := veblen (增元迭代 (ω加一元.跳出 (ω增元迭代 F)) n) ∅.. 1 in  
  G (lim f) = 递归 (λ ξ, lim (λ m, G (f m) ξ⁺)) (lim (λ m, G (f m) ∅)).
Proof.
  intros. unfold G. induction n. reflexivity.
  simpl in *. rewrite IHn. reflexivity.
Qed.

Lemma veblen_s_Z__Z_l_x : ∀ n (F : ω后继元 (S n)) α f,
  let G := veblen F α⁺ ∅ ∅.. 1 in
  G (lim f) = 递归 (λ ξ, lim (λ m, G (f m) ξ⁺)) (lim (λ m, G (f m) ∅)).
Proof.
  intros. unfold G. destruct n. reflexivity. simpl.
  rewrite <- f_Z_eq_f_z_Z, <- f_Z_eq_f_z_Z, 增元迭代_Z__Z_l_x. reflexivity.
Qed.

Lemma veblen_l_Z__Z_l_x : ∀ n (F : ω后继元 (S n)) f g,
  let G := veblen F (lim f) ∅ ∅.. 1 in
  G (lim g) = 递归 (λ ξ, lim (λ m, G (g m) ξ⁺)) (lim (λ m, G (g m) ∅)).
Proof.
  intros. unfold G. destruct n. reflexivity. simpl.
  rewrite <- f_Z_eq_f_z_Z, <- f_Z_eq_f_z_Z, 增元迭代_Z__Z_l_x. reflexivity.
Qed.

Lemma 增元迭代_x_Z__Z_l_y : ∀ n α f,
  let F := 增元迭代 (ω加一元.φ) n α ∅.. 1 in
  F (lim f) = 递归 (λ ξ, lim (λ m, F (f m) ξ⁺)) (lim (λ m, F (f m) ∅)).
Proof.
  intros. unfold F. destruct α.
  - induction n. reflexivity. simpl. rewrite veblen_z. apply IHn.
  - unfold 增元迭代. destruct n. reflexivity.
    rewrite f_Z_eq_f_z_Z, veblen_s_Z__Z_l_x. reflexivity.
  - unfold 增元迭代. destruct n. reflexivity.
    rewrite f_Z_eq_f_z_Z, veblen_l_Z__Z_l_x. reflexivity.
Qed.

Lemma 增元迭代_Z_s__Z : ∀ F n α,
  veblen (增元迭代 (ω加一元.跳出 (ω增元迭代 F)) n) ∅ ∅.._ α⁺ 0 ∅ =
  lim (λ m, veblen (增元迭代 (ω加一元.跳出 (ω增元迭代 F)) n) ∅ ∅.._ α m [1] ∅..).
Proof.
  intros. induction n. reflexivity.
  simpl in *. rewrite IHn. reflexivity.
Qed.

Lemma veblen_s_Z_s__Z : ∀ n (F : ω后继元 (S n)) α β,
  veblen F α⁺ ∅.._ β⁺ 0 ∅ = lim (λ m, veblen F α⁺ ∅.._ β m [1] ∅..).
Proof.
  intros. destruct n. reflexivity. simpl.
  rewrite 增元迭代_Z_s__Z. reflexivity.
Qed.

Lemma veblen_l_Z_s__Z : ∀ n (F : ω后继元 (S n)) f α,
  veblen F (lim f) ∅.._ α⁺ 0 ∅ = lim (λ m, veblen F (lim f) ∅.._ α m [1] ∅..).
Proof.
  intros. destruct n. reflexivity. simpl.
  rewrite 增元迭代_Z_s__Z. reflexivity.
Qed.

Lemma 增元迭代_x_Z_s__Z : ∀ n α β, 增元迭代 ω加一元.φ (S n) α ∅.._ β⁺ 0 ∅ =
  lim (λ m, 增元迭代 ω加一元.φ (S n) α ∅.._ β m [1] ∅..).
Proof.
  intros. destruct α.
  - induction n. reflexivity. simpl in *. rewrite veblen_z in *. apply IHn.
  - unfold 增元迭代. rewrite veblen_s_Z_s__Z. reflexivity.
  - unfold 增元迭代. rewrite veblen_l_Z_s__Z. reflexivity.
Qed.

Lemma 增元迭代_Z_l__Z : ∀ F n f,
  veblen (增元迭代 (ω加一元.跳出 (ω增元迭代 F)) n) ∅ ∅.._ (lim f) 0 ∅ =
  lim (λ m, veblen (增元迭代 (ω加一元.跳出 (ω增元迭代 F)) n) ∅ ∅.._ (f m) 0 ∅).
Proof.
  intros. induction n. reflexivity.
  simpl in *. rewrite IHn. reflexivity.
Qed.

Lemma veblen_s_Z_l__Z : ∀ n (F : ω后继元 (S n)) α f,
  veblen F α⁺ ∅.._ (lim f) 0 ∅ = lim (λ m, veblen F α⁺ ∅.._ (f m) 0 ∅).
Proof.
  intros. destruct n. reflexivity. simpl.
  rewrite 增元迭代_Z_l__Z. reflexivity.
Qed.

Lemma veblen_l_Z_l__Z : ∀ n (F : ω后继元 (S n)) f g,
  veblen F (lim f) ∅.._ (lim g) 0 ∅ = lim (λ m, veblen F (lim f) ∅.._ (g m) 0 ∅).
Proof.
  intros. destruct n. reflexivity. simpl.
  rewrite 增元迭代_Z_l__Z. reflexivity.
Qed.

Lemma 增元迭代_x_Z_l__Z : ∀ n α f, 增元迭代 ω加一元.φ (S n) α ∅.._ (lim f) 0 ∅ =
  lim (λ m, 增元迭代 ω加一元.φ (S n) α ∅.._ (f m) 0 ∅).
Proof.
  intros. destruct α.
  - induction n. reflexivity. simpl in *. rewrite veblen_z in *. apply IHn.
  - unfold 增元迭代. rewrite veblen_s_Z_l__Z. reflexivity.
  - unfold 增元迭代. rewrite veblen_l_Z_l__Z. reflexivity.
Qed.

Theorem φ_z_X : ∀ n, φ (S n) ∅ = φ n.
Proof. destruct n; reflexivity. Qed.

Theorem φ_s_Z__Z_x : ∀ n α, φ (S n) α⁺ ∅ ∅.. 0 = (λ β, φ (S n) α β ∅.. 0 ∅)′.
Proof. intros. unfold φ, 增元迭代. rewrite veblen_s_Z_x. reflexivity. Qed.

Theorem φ_l_Z__Z_x : ∀ n f, φ (S n) (lim f) ∅ ∅.. 0 =
  递归 (λ ξ, lim (λ m, φ (S n) (f m) ξ⁺ ∅.. 0 ∅)) (lim (λ m, φ (S n) (f m) ∅ ∅.. 0 ∅)).
Proof. intros. unfold φ, 增元迭代. rewrite veblen_l_Z_x. reflexivity. Qed.

Theorem φ_x_s_Z__Z_y : ∀ n α β, φ (S (S n)) α β⁺ ∅ ∅.. 0 = (λ γ, φ (S (S n)) α β γ ∅.. 0 ∅)′.
Proof. intros. unfold φ. rewrite 增元迭代_x_s_Z_y. reflexivity. Qed.

Theorem φ_x_l_Z__Z_y : ∀ n α f, φ (S (S n)) α (lim f) ∅ ∅.. 0 =
  递归 (λ ξ, lim (λ m, φ (S (S n)) α (f m) ξ⁺ ∅.. 0 ∅)) (lim (λ m, φ (S (S n)) α (f m) ∅ ∅.. 0 ∅)).
Proof. intros. unfold φ. rewrite 增元迭代_x_l_Z_y. reflexivity. Qed.

Theorem φ_x_Z__Z_s_y : ∀ n α β, φ n α ∅.. 1 β⁺ = (φ n α ∅.. 1 β)′.
Proof. intros. unfold φ. rewrite 增元迭代_x_Z__Z_s_y. reflexivity. Qed.

Theorem φ_x_Z__Z_l_y : ∀ n α f, φ n α ∅.. 1 (lim f) =
  递归 (λ ξ, lim (λ m, φ n α ∅.. 1 (f m) ξ⁺)) (lim (λ m, φ n α ∅.. 1 (f m) ∅)).
Proof. intros. unfold φ. rewrite 增元迭代_x_Z__Z_l_y. reflexivity. Qed.

Theorem φ_x_Z_s__Z : ∀ n α β, φ (S n) α ∅.._ β⁺ 0 ∅ =
  lim (λ m, φ (S n) α ∅.._ β m [1] ∅..).
Proof. intros. unfold φ. rewrite 增元迭代_x_Z_s__Z. reflexivity. Qed.

Theorem φ_x_Z_l__Z : ∀ n α f, φ (S n) α ∅.._ (lim f) 0 ∅ =
  lim (λ m, φ (S n) α ∅.._ (f m) 0 ∅).
Proof. intros. unfold φ. rewrite 增元迭代_x_Z_l__Z. reflexivity. Qed.

End ω2元.

Fixpoint ω倍数元 n : Set := match n with
  | O => 序数
  | S n => ∀ m, 多元 (S m) (ω倍数元 n)
end.

Notation ω2后继元 n := (多元 n ω2元).
Notation ω倍数后继元 n m := (多元 m (ω倍数元 n)).

Fact ω倍数元_1 : ω倍数元 1 = ω元.
Proof. reflexivity. Qed.

Fact ω倍数元_2 : ω倍数元 2 = ω2元.
Proof. reflexivity. Qed.

Fact ω倍数元_Sn : ∀ n, ω倍数元 (S n) = ∀ m, ω倍数后继元 n (S m).
Proof. reflexivity. Qed.

Notation ωω元 := (∀ n, ω倍数元 (S n)).

Module ω2加一元.

Fixpoint 跳出 (F : ω2元) (α : 序数) n : ω后继元 (S n).
  destruct α as [|α|f].
  - apply (F n).
  - set (lim (λ n, 跳出 F α n [1] ∅.. 0 ∅)) as G₀.
    set (λ ξ, lim (λ n, 跳出 F α n ξ⁺ ∅.. 0 ∅)) as G.
    apply (ω2元.增元迭代 (ω加一元.跳出 (ω增元迭代 (递归 G G₀))) n).
  - set (lim (λ n, 跳出 F (f n) 0 ∅ 0 ∅)) as G₀.
    set (λ ξ, lim (λ n, 跳出 F (f n) 0 ∅ 0 ξ⁺)) as G.
    apply (ω2元.增元迭代 (ω加一元.跳出 (ω增元迭代 (递归 G G₀))) n).
Defined.

Definition φ := 跳出 (ω2元.φ).

End ω2加一元.

Module ω3元.

Fixpoint veblen {n} : ω2后继元 (S n) → ω2后继元 (S (S n)).
  set (fix 增元迭代 (F : ω2后继元 1) n : ω2后继元 (S n) :=
    match n with
    | O => F
    | S m => veblen m (增元迭代 F m)
    end) as 增元迭代.
  refine (fix inner (F : ω2后继元 (S n)) (α : 序数) : ω2后继元 (S n) := _).
  destruct α as [|α|g].
  - apply F.
  - set (ω增元迭代 (λ β, inner F α β ∅.. 0 ∅ 0 ∅)′) as ω元F.
    apply (增元迭代 (ω2加一元.跳出 (ω2元.增元迭代 (ω加一元.跳出 ω元F)))).
  - set (lim (λ m, inner F (g m) ∅.. 0 ∅ 0 ∅)) as G₀.
    set (λ β, lim (λ m, inner F (g m) β⁺ ∅.. 0 ∅ 0 ∅)) as G.
    set (ω增元迭代 (递归 G G₀)) as ω元F.
    apply (增元迭代 (ω2加一元.跳出 (ω2元.增元迭代 (ω加一元.跳出 ω元F)))).
Defined.

Fixpoint 增元迭代 F n : ω2后继元 (S n) :=
  match n with
    | O => F
    | S m => veblen (增元迭代 F m)
  end.

Definition φ := 增元迭代 (ω2加一元.φ).

End ω3元.
