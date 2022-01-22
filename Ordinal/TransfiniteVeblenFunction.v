(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.WellFormed.
Require Import GOO.Ordinal.Recursion.
Require Import GOO.Ordinal.Iteration.
Require Import GOO.Ordinal.VeblenFunction.
Require Import GOO.Ordinal.ExtendedVeblenFunction.

Local Open Scope 序数域.

Definition 多元φ := ExtendedVeblenFunction.φ.

Module ω加1元.

Fixpoint φ α n : 多元函数 (S n) 序数 := match α with
  | ∅ => 多元φ n
  | α⁺ =>
    let α₀ := lim (λ n, φ α n [1] ∅..) in
    let f := λ β, lim (λ n, 多元φ n β⁺ ∅..) in
    广义多元φ (递归 f α₀) n
  | lim f =>
    let α₀ := lim (λ n, φ (f n) 0 ∅) in
    let f := λ β, lim (λ n, φ (f n) 0 β⁺) in
    广义多元φ (递归 f α₀) n
  end.

Fact φ_0atω : ∀ n, φ ∅ n = 多元φ n.
Proof. reflexivity. Qed.

Fact φ_1atω : φ [1] 0 ∅ = SVO.
Proof. reflexivity. Qed.

Theorem φ_Satω : ∀ α, φ α⁺ 0 ∅ = lim (λ n, φ α n [1] ∅..).
Proof. reflexivity. Qed.

Fact φ_1atω_1at0 : φ [1] 0 [1] = lim (λ n, 多元φ n SVO⁺ ∅..).
Proof. reflexivity. Qed.

Fact φ_Satω_1at0 : ∀ α, φ α⁺ 0 [1] = lim (λ n, 多元φ n (φ α⁺ 0 ∅)⁺ ∅..).
Proof. reflexivity. Qed.

Fact φ_Satω_Sat0 : ∀ α β, φ α⁺ 0 β⁺ = lim (λ n, 多元φ n (φ α⁺ 0 β)⁺ ∅..).
Proof. reflexivity. Qed.

Fact φ_Satω_Lat0 : ∀ α f, φ α⁺ 0 (lim f) = lim (λ n, φ α⁺ 0 (f n)).
Proof. reflexivity. Qed.

Fact φ_Satω_1at1_0at0 : ∀ α, φ α⁺ 1 [1] ∅ = Itω (φ α⁺ 0) ∅.
Proof. reflexivity. Qed.

Fact φ_Satω_1at1_Xat0 : ∀ α, φ α⁺ 1 [1] = (φ α⁺ 0)′.
Proof. reflexivity. Qed.

Fact φ_Satω_Sat1_Xat0 : ∀ α β, φ α⁺ 1 β⁺ = (φ α⁺ 1 β)′.
Proof. reflexivity. Qed.

Fact φ_Satω_Lat1_0at0 : ∀ α f, φ α⁺ 1 (lim f) ∅ = lim (λ n, φ α⁺ 1 (f n) ∅).
Proof. reflexivity. Qed.

Fact φ_Satω_Lat1_Sat0 : ∀ α f β, φ α⁺ 1 (lim f) β⁺ = lim (λ n, φ α⁺ 1 (f n) (φ α⁺ 1 (lim f) β)⁺).
Proof. reflexivity. Qed.

Fact φ_Satω_Lat1_Lat0 : ∀ α f g, φ α⁺ 1 (lim f) (lim g) = lim (λ n, φ α⁺ 1 (lim f) (g n)).
Proof. reflexivity. Qed.

Theorem φ_Satω_SatSn_Xat0 : ∀ α n β x, φ α⁺ (S n) β⁺ ∅.._ x = (λ ξ, φ α⁺ (S n) β ξ ∅..)′ x.
Proof. intros. unfold φ, 广义多元φ. rewrite veblen_s_Z_x. reflexivity. Qed.

Theorem φ_Satω_LatSn_Xat0 : ∀ α n f, φ α⁺ (S n) (lim f) ∅.._ =
  递归 (λ ξ, lim (λ m, φ α⁺ (S n) (f m) ξ⁺ ∅..)) (lim (λ m, φ α⁺ (S n) (f m) ∅ ∅..)).
Proof. intros. unfold φ, 广义多元φ. rewrite veblen_l_Z_x. reflexivity. Qed.

Corollary φ_Satω_LatSn_0at0 : ∀ α n f, φ α⁺ n (lim f) ∅.. = lim (λ m, φ α⁺ n (f m) ∅..).
Proof. intros. destruct n. reflexivity. rewrite f_Z_eq_f_Z_z, φ_Satω_LatSn_Xat0. reflexivity. Qed.

Corollary φ_Satω_LatSn_Sat0 : ∀ α n f β, φ α⁺ (S n) (lim f) ∅.._ β⁺ =
  lim (λ m, φ α⁺ (S n) (f m) (φ α⁺ (S n) (lim f) ∅.._ β)⁺ ∅..).
Proof. intros. rewrite φ_Satω_LatSn_Xat0. reflexivity. Qed.

Corollary φ_Satω_LatSn_Lat0 : ∀ α n f g, φ α⁺ (S n) (lim f) ∅.._ (lim g) =
  lim (λ m, φ α⁺ (S n) (lim f) ∅.._ (g m)).
Proof. intros. rewrite φ_Satω_LatSn_Xat0. reflexivity. Qed.

Theorem φ_Latω : ∀ f, φ (lim f) 0 ∅ = lim (λ n, φ (f n) 0 ∅).
Proof. reflexivity. Qed.

Fact φ_Latω_1at0 : ∀ f, φ (lim f) 0 [1] = lim (λ n, φ (f n) 0 (φ (lim f) 0 ∅)⁺).
Proof. reflexivity. Qed.

Fact φ_Latω_Sat0 : ∀ f α, φ (lim f) 0 α⁺ = lim (λ n, φ (f n) 0 (φ (lim f) 0 α)⁺).
Proof. reflexivity. Qed.

Fact φ_Latω_Lat0 : ∀ f g, φ (lim f) 0 (lim g) = lim (λ n, φ (lim f) 0 (g n)).
Proof. reflexivity. Qed.

Fact φ_Latω_1at1_0at0 : ∀ f, φ (lim f) 1 [1] ∅ = Itω (φ (lim f) 0) ∅.
Proof. reflexivity. Qed.

Fact φ_Latω_1at1_Xat0 : ∀ f, φ (lim f) 1 [1] = (φ (lim f) 0)′.
Proof. reflexivity. Qed.

Fact φ_Latω_Sat1_Xat0 : ∀ f α, φ (lim f) 1 α⁺ = (φ (lim f) 1 α)′.
Proof. reflexivity. Qed.

Fact φ_Latω_Lat1_0at0 : ∀ f g, φ (lim f) 1 (lim g) ∅ = lim (λ n, φ (lim f) 1 (g n) ∅).
Proof. reflexivity. Qed.

Fact φ_Latω_Lat1_Sat0 : ∀ f g α, φ (lim f) 1 (lim g) α⁺ = lim (λ n, φ (lim f) 1 (g n) (φ (lim f) 1 (lim g) α)⁺).
Proof. reflexivity. Qed.

Fact φ_Latω_Lat1_Lat0 : ∀ f g h, φ (lim f) 1 (lim g) (lim h) = lim (λ n, φ (lim f) 1 (lim g) (h n)).
Proof. reflexivity. Qed.

Theorem φ_Latω_SatSn_Xat0 : ∀ f n α x, φ (lim f) (S n) α⁺ ∅.._ x = (λ ξ, φ (lim f) (S n) α ξ ∅..)′ x.
Proof. intros. unfold φ, 广义多元φ. rewrite veblen_s_Z_x. reflexivity. Qed.

Theorem φ_Latω_LatSn_Xat0 : ∀ f n g, φ (lim f) (S n) (lim g) ∅.._ =
  递归 (λ ξ, lim (λ m, φ (lim f) (S n) (g m) ξ⁺ ∅..)) (lim (λ m, φ (lim f) (S n) (g m) ∅ ∅..)).
Proof. intros. unfold φ, 广义多元φ. rewrite veblen_l_Z_x. reflexivity. Qed.

Corollary φ_Latω_LatSn_0at0 : ∀ f n g, φ (lim f) n (lim g) ∅.. = lim (λ m, φ (lim f) n (g m) ∅..).
Proof. intros. destruct n. reflexivity. rewrite f_Z_eq_f_Z_z, φ_Latω_LatSn_Xat0. reflexivity. Qed.

Corollary φ_Latω_LatSn_Sat0 : ∀ f n g α, φ (lim f) (S n) (lim g) ∅.._ α⁺ =
  lim (λ m, φ (lim f) (S n) (g m) (φ (lim f) (S n) (lim g) ∅.._ α)⁺ ∅..).
Proof. intros. rewrite φ_Latω_LatSn_Xat0. reflexivity. Qed.

Corollary φ_Latω_LatSn_Lat0 : ∀ f n g h, φ (lim f) (S n) (lim g) ∅.._ (lim h) =
  lim (λ m, φ (lim f) (S n) (lim g) ∅.._ (h m)).
Proof. intros. rewrite φ_Latω_LatSn_Xat0. reflexivity. Qed.

Example φ_Sωatω : φ ω⁺ 0 ∅ = lim (λ n, φ ω n [1] ∅..).
Proof. reflexivity. Qed.

Example φ_φ_1atω_atω : φ (φ [1] 0 ∅) 0 ∅ = lim (λ n, φ (多元φ n [1] ∅..) 0 ∅).
Proof. reflexivity. Qed.

End ω加1元.
