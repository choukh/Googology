(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.Recursion.
Require Import GOO.Ordinal.Arithmetic.
Require Import GOO.Ordinal.Iteration.
Require Import GOO.Ordinal.VeblenFunction.

Local Open Scope 序数域.
Local Open Scope 序数算术域.

Fixpoint 序元 ι :=
  match ι with
  | ∅ => 序数
  | ι⁺ => 序数 → 序元 ι
  | lim f => ∀ n, 序数 → 序元 (f n)
  end.

Reserved Notation "F '∅..'" (at level 20).
Fixpoint 充零 {ι} (F : 序元 ι) : 序数 :=
  match ι, F with
  | ∅, F => F
  | _⁺, F => F ∅ ∅..
  | lim _, F => F 0 ∅ ∅..
  end
where "F ∅.." := (充零 F) : 序数域.

Reserved Notation "F '∅.._'" (at level 20).
Fixpoint 充零留一 {ι} (F : 序元 ι⁺) : 序元 [1] :=
  match ι, F with
  | ∅, F => F
  | _⁺, F => F ∅ ∅.._
  | lim _, F => F ∅ 0 ∅.._
  end
where "F ∅.._" := (充零留一 F) : 序数域.

Fixpoint veblen {ι} : 序元 ι⁺ → 序元 ι⁺⁺.
  assert (增元迭代: 序元 [1] → ∀ ι, 序元 ι⁺). {
    refine (fix 增元迭代 (F₁ : 序元 [1]) ι : 序元 ι⁺ := _).
    destruct ι as [|ι|f].
    - apply F₁.
    - apply (veblen ι (增元迭代 F₁ ι)).
    - assert (跳出: 序元 (lim f) → 序元 (lim f)⁺). {
        refine (fix 跳出 (F : 序元 (lim f)) α n : 序元 (f n)⁺ := _).
        destruct α as [|α|g].
        - simpl. apply F.
        - set (lim (λ m, 跳出 F α m [1] ∅..)) as G₀.
          set (λ ξ, lim (λ m, 跳出 F α m ξ⁺ ∅..)) as G.
          apply (增元迭代 (递归 G G₀) (f n)).
        - set (lim (λ m, 跳出 F (g m) 0 ∅..)) as G₀.
          set (λ ξ, lim (λ m, 跳出 F (g m) 0 ∅.._ ξ⁺)) as G.
          apply (增元迭代 (递归 G G₀) (f n)).
      }
      apply 跳出. intros n. apply 增元迭代. apply F₁.
  }
  refine (fix veblen (F : 序元 ι⁺) (α : 序数) : 序元 ι⁺ := _).
  destruct α as [|α|f].
  - apply F.
  - apply (增元迭代 (λ β, veblen F α β ∅..)′ ι).
  - set (lim (λ m, veblen F (f m) ∅..)) as G₀.
    set (λ β, lim (λ m, veblen F (f m) β⁺ ∅..)) as G.
    apply (增元迭代 (递归 G G₀) ι).
Defined.

Fixpoint 增元迭代 (F₁ : 序元 [1]) ι : 序元 ι⁺.
  destruct ι as [|ι|f].
  - apply F₁.
  - apply (veblen (增元迭代 F₁ ι)).
  - assert (跳出: 序元 (lim f) → 序元 (lim f)⁺). {
      refine (fix 跳出 (F : 序元 (lim f)) α n : 序元 (f n)⁺ := _).
      destruct α as [|α|g].
      - simpl. apply F.
      - set (lim (λ m, 跳出 F α m [1] ∅..)) as G₀.
        set (λ ξ, lim (λ m, 跳出 F α m ξ⁺ ∅..)) as G.
        apply (增元迭代 (递归 G G₀) (f n)).
      - set (lim (λ m, 跳出 F (g m) 0 ∅..)) as G₀.
        set (λ ξ, lim (λ m, 跳出 F (g m) 0 ∅.._ ξ⁺)) as G.
        apply (增元迭代 (递归 G G₀) (f n)).
    }
    apply 跳出. intros n. apply 增元迭代. apply F₁.
Defined.

Definition φ : ∀ ι, 序数 → 序元 ι := 增元迭代 (cantor ∅).

Definition SVO := φ ω [1] ∅...
Definition LVO := (λ ξ, φ ξ [1] ∅..)′ ∅.

Lemma f_Z_eq_f_Z_z : ∀ ι (F : 序元 ι⁺), F ∅.. = F ∅.._ ∅.
Proof.
  intros. induction ι as [|ι IH|f IH]; simpl.
  - reflexivity.
  - rewrite <- IH. reflexivity.
  - rewrite <- IH. reflexivity.
Qed.

Lemma f_Z_eq_f_z_Z : ∀ ι (F : 序元 ι⁺), F ∅.. = F ∅ ∅...
Proof.
  intros. induction ι as [|ι IH|f IH]; simpl.
  - reflexivity.
  - rewrite <- IH. reflexivity.
  - rewrite <- IH. reflexivity.
Qed.

Lemma veblen_z : ∀ ι (F : 序元 ι⁺), veblen F ∅ = F.
Proof. destruct ι; reflexivity. Qed.

Lemma 增元迭代_Z_x : ∀ F ι, (增元迭代 F ι) ∅.._ = F.
Proof.
  intros. induction ι as [|ι IH|f IH]; simpl.
  - reflexivity.
  - rewrite veblen_z, IH. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma veblen_s_Z_x : ∀ ι (F : 序元 ι⁺) α,
  veblen F α⁺ ∅.._ = (λ β, veblen F α β ∅..)′.
Proof.
  intros. destruct ι as [| |f].
  - reflexivity.
  - simpl. rewrite veblen_z. rewrite 增元迭代_Z_x. reflexivity.
  - simpl. rewrite 增元迭代_Z_x. reflexivity.
Qed.

Lemma veblen_l_Z_x : ∀ ι (F : 序元 ι⁺) f, veblen F (lim f) ∅.._ =
  递归 (λ ξ, lim (λ m, veblen F (f m) ξ⁺ ∅..)) (lim (λ m, veblen F (f m) ∅ ∅..)).
Proof.
  intros. destruct ι as [| |g].
  - reflexivity.
  - simpl. rewrite veblen_z. rewrite 增元迭代_Z_x. reflexivity.
  - simpl. rewrite 增元迭代_Z_x. reflexivity.
Qed.

Theorem φ_z : φ ∅ = cantor ∅.
Proof. reflexivity. Qed.

Theorem φ_s_z_X : ∀ ι, φ ι⁺ ∅ = φ ι.
Proof. intros. unfold φ. simpl. rewrite veblen_z. reflexivity. Qed.

Theorem φ_s_s_Z_x : ∀ ι α, φ ι⁺ α⁺ ∅.._ = (λ β, φ ι⁺ α β ∅..)′.
Proof. intros. unfold φ, 增元迭代. rewrite veblen_s_Z_x. reflexivity. Qed.

Theorem φ_s_l_Z_x : ∀ ι f, φ ι⁺ (lim f) ∅.._ =
  递归 (λ ξ, lim (λ m, φ ι⁺ (f m) ξ⁺ ∅..)) (lim (λ m, φ ι⁺ (f m) ∅ ∅..)).
Proof. intros. unfold φ, 增元迭代. rewrite veblen_l_Z_x. reflexivity. Qed.

Theorem φ_l_z_X : ∀ f, φ (lim f) ∅ = λ n, φ (f n).
Proof. reflexivity. Qed.

Theorem φ_l_s_Z_x : ∀ f α, φ (lim f) α⁺ 0 ∅.._ =
  递归 (λ ξ, (lim (λ n, φ (lim f) α n ξ⁺ ∅..))) (lim (λ n, φ (lim f) α n [1] ∅..)).
Proof. intros. unfold φ. simpl. rewrite 增元迭代_Z_x. reflexivity. Qed.

Corollary φ_l_s_Z : ∀ f α, φ (lim f) α⁺ ∅.. =
  lim (λ n, φ (lim f) α n [1] ∅..).
Proof. intros. simpl. rewrite <- f_Z_eq_f_z_Z, f_Z_eq_f_Z_z, φ_l_s_Z_x. reflexivity. Qed.

Corollary φ_l_s_Z_s : ∀ f α β, φ (lim f) α⁺ 0 ∅.._ β⁺ =
  lim (λ n, φ (lim f) α n (φ (lim f) α⁺ 0 ∅.._ β)⁺ ∅..).
Proof. intros. rewrite φ_l_s_Z_x. reflexivity. Qed.

Corollary φ_l_s_Z_l : ∀ f α g, φ (lim f) α⁺ 0 ∅.._ (lim g) =
  lim (λ m, φ (lim f) α⁺ 0 ∅.._ (g m)).
Proof. intros. rewrite φ_l_s_Z_x. reflexivity. Qed.

Theorem φ_l_l_Z_x : ∀ f g, φ (lim f) (lim g) 0 ∅.._ =
  递归 (λ ξ, (lim (λ n, φ (lim f) (g n) 0 ∅.._ ξ⁺))) (lim (λ n, φ (lim f) (g n) 0 ∅ ∅..)).
Proof. intros. unfold φ. simpl. rewrite 增元迭代_Z_x. reflexivity. Qed.

Corollary φ_l_l_Z : ∀ f g, φ (lim f) (lim g) 0 ∅ ∅.. =
  lim (λ n, φ (lim f) (g n) 0 ∅ ∅..).
Proof. intros. rewrite <- f_Z_eq_f_z_Z, f_Z_eq_f_Z_z, φ_l_l_Z_x. reflexivity. Qed.

Corollary φ_l_l_Z_s : ∀ f g α, φ (lim f) (lim g) 0 ∅.._ α⁺ =
  lim (λ n, φ (lim f) (g n) 0 ∅.._ (φ (lim f) (lim g) 0 ∅.._ α)⁺).
Proof. intros. rewrite φ_l_l_Z_x. reflexivity. Qed.

Corollary φ_l_l_Z_l : ∀ f g h, φ (lim f) (lim g) 0 ∅.._ (lim h) =
  lim (λ n, φ (lim f) (lim g) 0 ∅.._ (h n)).
Proof. intros. rewrite φ_l_l_Z_x. reflexivity. Qed.
