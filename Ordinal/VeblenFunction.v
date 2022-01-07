(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.Operation.
Require Import GOO.Ordinal.Recursion.
Require Import GOO.Ordinal.Arithmetic.
Require Import GOO.Ordinal.Iteration.
Require Import GOO.Ordinal.EpsilonNumbers.

Local Open Scope 序数域.
Local Open Scope 序数算术域.

Fixpoint cantor (α₀ α : 序数) : 序数 :=
  match α with
  | ∅ => α₀⁺
  | α⁺ => Itω (λ ξ, cantor ξ α) α₀
  | lim f => lim (λ n, cantor α₀ (f n))
  end.

Fact cantor_零 : ∀ α, cantor α [0] = α⁺.
Proof. easy. Qed.

Lemma cantor_Sn : ∀ α n, cantor α [S n] = Itω (λ ξ, cantor ξ [n]) α.
Proof. easy. Qed.

Fact cantor_1 : ∀ α, cantor α [1] ≃ α + ω.
Proof. intros. rewrite cantor_Sn. rewrite 无穷迭代弱等于无穷递归. easy. Qed.

Local Arguments cantor : simpl never.

Fact cantor_2 : ∀ α, cantor α [2] ≃ α + ω * ω.
Proof.
  intros. rewrite cantor_Sn. rewrite 无穷迭代弱等于无穷递归.
  simpl. unfold ω at 2. rewrite 乘极限, 加极限.
  split; constructor; intros n; apply 弱序_极限_介入 with n.
  - induction n; simpl.
    + rewrite 乘零, 加零. easy.
    + rewrite cantor_1, 乘后继, <- 加法结合律.
      eapply 弱序_传递. 2: reflexivity. apply 加法_弱保序_左, IHn.
  - induction n; simpl.
    + rewrite 乘零, 加零. easy.
    + rewrite cantor_1, 乘后继, <- 加法结合律.
      eapply 弱序_传递. 2: reflexivity. apply 加法_弱保序_左, IHn.
Qed.

Lemma cantor_后继 : ∀ α₀ α, cantor α₀ α⁺ = Itω (λ ξ, cantor ξ α) α₀.
Proof. easy. Qed.

Lemma cantor_极限 : ∀ α₀ f, cantor α₀ (lim f) = lim (λ n, cantor α₀ (f n)).
Proof. easy. Qed.

Lemma cantor_α : ∀ α₀ α, cantor α₀ α ≃ α₀ + ω ^ α.
Proof.
  intros. revert α₀. induction α as [|α IH|f IH]; intros α₀.
  - rewrite 零次幂, 加一. easy.
  - rewrite 后继次幂, cantor_后继.
    unfold ω. rewrite 乘极限, 加极限.
    split; constructor; intros n; apply 弱序_极限_介入 with n.
    + induction n; simpl.
      * rewrite 乘零, 加零. easy.
      * rewrite IH, 乘后继, <- 加法结合律.
        eapply 弱序_传递. 2: reflexivity. apply 加法_弱保序_左, IHn.
    + induction n; simpl.
      * rewrite 乘零, 加零. easy.
      * rewrite IH, 乘后继, <- 加法结合律.
        eapply 弱序_传递. 2: reflexivity. apply 加法_弱保序_左, IHn.
  - rewrite cantor_极限, 极限次幂, 加极限.
    split; constructor; intros n; apply 弱序_极限_介入 with n; rewrite IH; easy.
Qed.

Lemma cantor0 : ∀ α, cantor ∅ α ≃ ω ^ α.
Proof. intros. simpl. rewrite cantor_α, 加于零. easy. Qed.

Lemma cantor0为序数嵌入 : 序数嵌入 (cantor ∅).
Proof.
  split3. 3: auto.
  - intros α β H. rewrite cantor0, cantor0. apply 幂运算_弱保序_右; auto.
  - intros α β H. eapply 弱强传递. apply cantor0.
    eapply 强弱传递. 2: apply cantor0. apply 幂运算_强保序_右; auto.
Qed.

Module 二元.

Fixpoint veblen f α :=
  match α with
  | ∅ => f
  | α⁺ => (veblen f α)′
  | lim g => λ β, lim (λ n, veblen f (g n) β)
  end.

Definition φ := veblen (cantor ∅).

Definition Γ := (λ ξ, φ ξ ∅)′.

Theorem φ_零 : ∀ α, φ [0] α ≃ ω ^ α.
Proof. intros. simpl. unfold φ, veblen. rewrite cantor0. easy. Qed.

Fact φ_后继 : ∀ α₀ α, φ α⁺ α₀ = (φ α)′ α₀.
Proof. easy. Qed.

Fact φ_极限 : ∀ α₀ f, φ (lim f) α₀ = lim (λ n, φ (f n) α₀).
Proof. easy. Qed.

Remark φ_1 : ∀ α, φ [1] α ≃ ε α.
Proof.
  intros. simpl. apply 不动点枚举保函数外延.
  - apply cantor0为序数嵌入.
  - apply 幂运算为序数嵌入. auto.
  - apply φ_零.
Qed.

Remark φ_2 : ∀ α, φ [2] α ≃ ζ α.
Proof.
  intros. simpl. apply 不动点枚举保函数外延.
  - apply 不动点枚举为序数嵌入. apply cantor0为序数嵌入.
  - apply ε为序数嵌入.
  - apply φ_1.
Qed.

Remark φ_3 : ∀ α, φ [3] α ≃ η α.
Proof.
  intros. simpl. apply 不动点枚举保函数外延.
  - apply 不动点枚举为序数嵌入_递进, 不动点枚举为序数嵌入. apply cantor0为序数嵌入.
  - apply ζ为序数嵌入.
  - apply φ_2.
Qed.

Definition ε1 := Γ′.
Definition ζ1 := ε1′.
Definition η1 := ζ1′.

Definition φ1 := veblen Γ.
Definition Γ1 := (λ ξ, φ1 ξ ∅)′.

Definition ε2 := Γ1′.
Definition ζ2 := ε2′.
Definition η2 := ζ2′.

Definition φ2 := veblen Γ1.
Definition Γ2 := (λ ξ, φ2 ξ ∅)′.

End 二元.

Module 三元.

Fixpoint veblen f α :=
  match α with
  | ∅ => f
  | α⁺ => 二元.veblen (λ β, veblen f α β ∅)′
  | lim g => λ β γ, lim (λ n, veblen f (g n) β γ)
  end.

Definition φ := veblen 二元.φ.

Fact φ_1_0_γ : ∀ γ, φ [1] [0] γ = 二元.Γ γ.
Proof. reflexivity. Qed.

Fact φ_1_1_γ : ∀ γ, φ [1] [1] γ = 二元.ε1 γ.
Proof. reflexivity. Qed.

Fact φ_1_2_γ : ∀ γ, φ [1] [2] γ = 二元.ζ1 γ.
Proof. reflexivity. Qed.

Fact φ_1_3_γ : ∀ γ, φ [1] [3] γ = 二元.η1 γ.
Proof. reflexivity. Qed.

Fact φ_1_ω_γ : ∀ γ, φ [1] ω γ = 二元.φ1 ω γ.
Proof. reflexivity. Qed.

Fact φ_2_0_γ : ∀ γ, φ [2] [0] γ = 二元.Γ1 γ.
Proof. reflexivity. Qed.

Fact φ_2_1_γ : ∀ γ, φ [2] [1] γ = 二元.ε2 γ.
Proof. reflexivity. Qed.

Fact φ_2_2_γ : ∀ γ, φ [2] [2] γ = 二元.ζ2 γ.
Proof. reflexivity. Qed.

Fact φ_2_3_γ : ∀ γ, φ [2] [3] γ = 二元.η2 γ.
Proof. reflexivity. Qed.

Fact φ_2_ω_γ : ∀ γ, φ [2] ω γ = 二元.φ2 ω γ.
Proof. reflexivity. Qed.

Fact φ_3_0_γ : ∀ γ, φ [3] [0] γ = 二元.Γ2 γ.
Proof. reflexivity. Qed.

Fact φ_极限 : ∀ f β γ, φ (lim f) β γ = lim (λ n, φ (f n) β γ).
Proof. reflexivity. Qed.

End 三元.

Module 四元.

Fixpoint veblen f α :=
  match α with
  | ∅ => f
  | α⁺ => 三元.veblen (二元.veblen (λ β, veblen f α β ∅ ∅)′)
  | lim g => λ β γ δ, lim (λ n, veblen f (g n) β γ δ)
  end.

Definition φ := veblen 三元.φ.

Fact φ_1_0_0_0 : φ [1] [0] [0] [0] = (λ α, 三元.φ α ∅ ∅)′ ∅.
Proof. reflexivity. Qed.

Fact φ_1_0_0_1 : φ [1] [0] [0] [1] = Itω (λ α, 三元.φ α ∅ ∅) (φ [1] [0] [0] [0])⁺.
Proof. reflexivity. Qed.

Fact φ_1_0_0_2 : φ [1] [0] [0] [2] = Itω (λ α, 三元.φ α ∅ ∅) (φ [1] [0] [0] [1])⁺.
Proof. reflexivity. Qed.

Fact φ_1_0_0_ω : φ [1] [0] [0] ω = lim (λ n, φ [1] [0] [0] [n]).
Proof. reflexivity. Qed.

Fact φ_1_0_0_φ_1_0_0_0 : φ [1] [0] [0] (φ [1] [0] [0] [0]) =
  lim (λ n, φ [1] [0] [0] (迭代 (λ α, 三元.φ α ∅ ∅) ∅ n)).
Proof. reflexivity. Qed.

Fact φ_1_0_1_0 : φ [1] [0] [1] [0] = Itω (λ δ, φ [1] [0] [0] δ) ∅.
Proof. reflexivity. Qed.

Fact φ_1_0_ω_0 : φ [1] [0] ω [0] = lim (λ n, φ [1] [0] [n] [0]).
Proof. reflexivity. Qed.

Fact φ_1_1_0_0 : φ [1] [1] [0] [0] = Itω (λ γ, φ [1] [0] γ [0]) ∅.
Proof. reflexivity. Qed.

Fact φ_2_0_0_0 : φ [2] [0] [0] [0] = Itω (λ β, φ [1] β [0] [0]) ∅.
Proof. reflexivity. Qed.

Lemma φ_极限 : ∀ f β γ δ, φ (lim f) β γ δ = lim (λ n, φ (f n) β γ δ).
Proof. reflexivity. Qed.

End 四元.
