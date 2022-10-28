(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.WellFormed.
Require Import GOO.Ordinal.Operation.
Require Import GOO.Ordinal.Recursion.
Require Import GOO.Ordinal.Arithmetic.
Require Import GOO.Ordinal.Tetration.

Local Open Scope 序数域.
Local Open Scope 序数算术域.

Fixpoint 迭代 {A : Type} (F : A → A) (a : A) (n : nat) : A :=
  match n with
  | O => a
  | S n => F (迭代 F a n)
  end.

Lemma 有穷迭代等于有限递归 : ∀ F α n, 迭代 F α n = 递归 F α [n].
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Definition 无穷迭代 F := λ α, lim (λ n, 迭代 F α n).
Notation Itω := 无穷迭代.

Lemma 无穷迭代弱等于无穷递归 : ∀ F α, Itω F α ≃ 递归 F α ω.
Proof.
  intros. unfold Itω. simpl. split; constructor; intros n;
  apply 弱序_极限_介入 with n; rewrite 有穷迭代等于有限递归; reflexivity.
Qed.

Lemma 无穷迭代_弱放大 : ∀ F, 弱放大 F → 弱放大 (Itω F).
Proof. intros. apply 弱序_极限_介入 with 1. apply H. Qed.

Lemma 无穷迭代_弱保序 : ∀ F, 弱放大 F → 弱保序 F → 弱保序 (Itω F).
Proof.
  intros F Asc OP * H. constructor. intros n.
  apply 弱序_极限_介入 with (S n). simpl.
  apply 弱序_传递 with (迭代 F β n).
  - induction n; simpl. apply H. apply OP. apply IHn.
  - apply Asc.
Qed.

Section Veblen不动点.
Variable F : 序数 → 序数.
Variable F嵌入 : 序数嵌入 F.

Local Lemma F连续 : 极限处连续 F.
Proof. apply F嵌入. Qed.

Local Lemma F弱放大 : 弱放大 F.
Proof. apply 序数嵌入弱放大. apply F嵌入. Qed.

(* 序数嵌入的无穷迭代为不动点 *)
Lemma 不动点为之 : ∀ α, F (Itω F α) ≃ Itω F α.
Proof.
  intros. unfold Itω.
  rewrite F连续. split; constructor; intros n.
  - apply 弱序_极限_介入 with (S n). simpl. reflexivity.
  - apply 弱序_极限_介入 with n. apply F弱放大.
Qed.

Lemma 不动点任意大 : ∀ α, α ≤ Itω F α.
Proof. intros. apply 弱序_极限_介入 with 0. simpl. reflexivity. Qed.

(* 序数嵌入存在任意大的不动点 *)
Theorem Veblen不动点定理 : ∀ α, ∃ β, F β ≃ β ∧ α ≤ β.
Proof. intros. exists (Itω F α). split. apply 不动点为之. apply 不动点任意大. Qed.

Definition 最小不动点 F := Itω F ∅.
Local Notation "F ⁰" := (最小不动点 F) (format "F ⁰", at level 6).

Theorem 最小不动点为之 : F F⁰ ≃ F⁰ ∧ ∀ α, F α ≃ α → F⁰ ≤ α.
Proof.
  split. apply 不动点为之. intros. constructor.
  induction n; simpl. constructor.
  rewrite <- H. apply F嵌入. apply IHn.
Qed.

Lemma 最小迭代序列递增 : 零处强放大 F → 递增序列 (迭代 F ∅).
Proof.
  intros Asc n m Hnm. induction m.
  - easy.
  - simpl. inversion_clear Hnm.
    + clear IHm. induction m. simpl. apply Asc. simpl. apply F嵌入. apply IHm.
    + eapply 强弱传递. apply IHm. apply H. apply F弱放大.
Qed.

Theorem 最小不动点良构 : 零处强放大 F → 保良构 F → 良构 F⁰.
Proof.
  intros Asc WF. split.
  - induction n. easy. simpl. apply WF. apply IHn.
  - apply 最小迭代序列递增. apply Asc.
Qed.

Definition 后继不动点 F α := Itω F α⁺.
Local Notation "F ¹" := (后继不动点 F) (format "F ¹", at level 6).

Theorem 后继不动点为之 : ∀ α, F (F¹ α) ≃ F¹ α ∧ α < F¹ α ∧ ∀ γ, F γ ≃ γ → α < γ → F¹ α ≤ γ.
Proof.
  split3. apply 不动点为之. apply 小于即后继小于等于. apply 不动点任意大.
  intros γ FP H. constructor. induction n; simpl.
  - apply 小于即后继小于等于. apply H.
  - rewrite <- FP. apply F嵌入. apply IHn.
Qed.

Lemma 后继不动点_弱放大 : 弱放大 F¹.
Proof. intros. apply 弱序_后继_除去. apply 无穷迭代_弱放大. apply F弱放大. Qed.

Lemma 后继不动点_弱保序 : 弱保序 F¹.
Proof. intros. apply 无穷迭代_弱保序. apply F弱放大. apply F嵌入. rewrite <- 后继_弱保序. easy. Qed.

Lemma 后继不动点_强放大 : 强放大 F¹.
Proof. intros. eapply 强序_极限_介入 with 0. simpl. easy. Qed.

Lemma 后继迭代序列递增 : ∀ α, 良构 α → 良构后继处强放大 F → 递增序列 (迭代 F α⁺).
Proof.
  intros α WF Asc n m Hnm. induction m.
  - easy.
  - simpl. inversion_clear Hnm.
    + clear IHm. induction m. simpl. apply Asc. apply WF.
      simpl. apply F嵌入. apply IHm.
    + eapply 强弱传递. apply IHm. apply H. apply F弱放大.
Qed.

Lemma 后继不动点_保良构 : 良构后继处强放大 F → 保良构 F → 保良构 F¹.
Proof.
  intros Asc WF α WFα. split.
  - induction n; simpl. apply WFα. apply WF. apply IHn.
  - apply 后继迭代序列递增. apply WFα. apply Asc.
Qed.

End Veblen不动点.

Notation "F ⁰" := (最小不动点 F) (format "F ⁰", at level 6) : 序数域.
Notation "F ¹" := (后继不动点 F) (format "F ¹", at level 6) : 序数域.

Definition 不动点枚举 F := 递归 F¹ F⁰.
Notation "F ′" := (不动点枚举 F) (format "F ′", at level 6) : 序数域.

Theorem 不动点枚举保函数外延 : ∀ f g, 序数嵌入 f → 序数嵌入 g → 
  (∀ α, f α ≃ g α) → ∀ α, f′ α ≃ g′ α.
Proof with auto.
  intros * Ef Eg Heq. unfold 不动点枚举.
  induction α as [|α IH|h IH].
  - split; constructor; intros n; simpl.
    + induction n. constructor.
      simpl. unfold 最小不动点. rewrite Heq, <- 不动点为之... apply Eg...
    + induction n. constructor.
      simpl. unfold 最小不动点. rewrite <- Heq, <- 不动点为之... apply Ef...
  - simpl. split; constructor; intros n.
    + induction n; simpl.
      * apply 弱序_极限_介入 with 0. simpl. rewrite <- 后继_弱保序, IH. easy.
      * unfold 后继不动点 at 2. rewrite Heq, <- 不动点为之... apply Eg...
    + induction n; simpl.
      * apply 弱序_极限_介入 with 0. simpl. rewrite <- 后继_弱保序, IH. easy.
      * unfold 后继不动点 at 2. rewrite <- Heq, <- 不动点为之... apply Ef...
  - simpl. split; constructor; intros n; apply 弱序_极限_介入 with n; apply IH.
Qed.

Section 不动点枚举.
Variable F : 序数 → 序数.
Variable F嵌入 : 序数嵌入 F.
Variable Asc0 : 零处强放大 F.
Variable Asc1 : 良构后继处强放大 F.

Lemma 不动点枚举_零 : F′ ∅ = F⁰.
Proof. easy. Qed.

Lemma 不动点枚举_后继 : ∀ α, F′ α⁺ = Itω F (F′ α)⁺.
Proof. easy. Qed.

Lemma 不动点枚举_极限 : ∀ f, F′ (lim f) = lim (λ n, F′ (f n)).
Proof. easy. Qed.

Theorem 不动点枚举枚举之 : ∀ α, F (F′ α) ≃ F′ α.
Proof.
  induction α as [| |f IH].
  - rewrite 不动点枚举_零. apply 不动点为之. auto.
  - rewrite 不动点枚举_后继. apply 不动点为之. auto.
  - rewrite 不动点枚举_极限. destruct F嵌入 as [_ [_ Conti]]. rewrite Conti.
    split; constructor; intros n; eapply 弱序_极限_介入; rewrite IH; reflexivity.
Qed.

Theorem 不动点枚举为序数嵌入 : 序数嵌入 F′.
Proof.
  split3.
  - apply 递归_弱保序_右.
    + apply 后继不动点_弱放大. apply F嵌入.
    + apply 后继不动点_弱保序. apply F嵌入.
  - apply 递归_强保序_右.
    + apply 后继不动点_强放大.
    + apply 后继不动点_弱保序. apply F嵌入.
  - easy.
Qed.

Corollary 存在不动点的不动点 : ∀ α, ∃ β, F′ β ≃ β ∧ α ≤ β.
Proof. intros. apply Veblen不动点定理. apply 不动点枚举为序数嵌入. Qed.

Corollary 不动点枚举在后继处递增 : 后继处递增 F′.
Proof. apply 强保序在后继处递增. apply 不动点枚举为序数嵌入. Qed.

Theorem 不动点枚举保良构 : 保良构 F → 保良构 F′.
Proof.
  intros WF. apply 递归保良构.
  - apply 后继不动点_强放大.
  - apply 后继不动点_弱保序. apply F嵌入.
  - apply 后继不动点_保良构. apply F嵌入. apply Asc1. apply WF.
  - apply 最小不动点良构. apply F嵌入. apply Asc0. apply WF.
Qed.

Lemma 不动点枚举在零处强放大 : 零处强放大 F′.
Proof.
  unfold 不动点枚举. simpl. unfold 最小不动点.
  eapply 强序_极限_介入 with 1. simpl. apply Asc0.
Qed.

Lemma 不动点枚举在良构后继处强放大 : 良构后继处强放大 F′.
Proof.
  intros α WFα. unfold 不动点枚举. simpl. apply 强弱传递 with (F¹ α).
  - unfold 后继不动点. eapply 强序_极限_介入 with 1. simpl. apply Asc1. apply WFα.
  - apply 后继不动点_弱保序. apply F嵌入. apply 递归_弱放大_左.
    apply 后继不动点_强放大. apply 后继不动点_弱保序. apply F嵌入.
Qed.

Theorem 不动点枚举保良构_递进 : 保良构 F′ → 保良构 F′′.
Proof.
  intros WF. apply 递归保良构.
  - apply 后继不动点_强放大.
  - apply 后继不动点_弱保序. apply 不动点枚举为序数嵌入.
  - apply 后继不动点_保良构. apply 不动点枚举为序数嵌入.
    apply 不动点枚举在良构后继处强放大. apply WF.
  - apply 最小不动点良构. apply 不动点枚举为序数嵌入.
    apply 不动点枚举在零处强放大. apply WF.
Qed.

Lemma 不动点飞升 : ∀ n, F [n] < F′ ∅.
Proof.
  intros. unfold 不动点枚举, 递归, 最小不动点.
  apply 强弱传递 with (F [S n]). apply F嵌入. simpl. auto.
  apply 弱序_极限_介入 with (S (S n)). simpl. apply F嵌入.
  induction n; simpl.
  - apply 小于即后继小于等于. apply Asc0.
  - apply F嵌入 in IHn. eapply 弱序_传递. 2: apply IHn.
    apply 小于即后继小于等于. apply Asc1. apply 有限序数良构.
Qed.

End 不动点枚举.

Theorem 不动点枚举为序数嵌入_递进 : ∀ F, 序数嵌入 F′ → 序数嵌入 F′′.
Proof. intros F. apply 不动点枚举为序数嵌入. Qed.

Section 左加法不动点.
Variable ξ : 序数.

Definition σ := (加法 ξ)′.

Lemma σ数为左加法不动点 : ∀ α, ξ + (σ α) ≃ σ α.
Proof. apply 不动点枚举枚举之. apply 加法为序数嵌入. Qed.

Lemma σ_零 : σ [0] ≃ ξ * ω.
Proof.
  intros. unfold ω. rewrite 乘极限.
  split; constructor; intros n; apply 弱序_极限_介入 with n; (
    induction n; [reflexivity|
      simpl; rewrite 乘后继, <- 加法有限结合律; apply 加法_弱保序_右; apply IHn
  ]).
Qed.

Lemma σ_后继 : ∀ α, σ α⁺ ≃ (σ α)⁺.
Proof.
  intros. split.
  - unfold σ. rewrite 不动点枚举_后继. constructor. induction n.
    + simpl. easy.
    + simpl. apply 弱序_传递 with (ξ + (σ α)⁺). apply 加法_弱保序_右. apply IHn.
      rewrite 加后继, <- 后继_弱保序, σ数为左加法不动点. reflexivity.
  - apply 小于即后继小于等于. apply 不动点枚举在后继处递增. apply 加法为序数嵌入.
Qed.

Lemma σ_极限 : ∀ f, σ (lim f) ≃ lim (λ n, σ (f n)).
Proof. easy. Qed.

Theorem σ表达式 : ∀ α, σ α ≃ ξ * ω + α.
Proof.
  induction α as [| |f IH].
  - rewrite 加零. apply σ_零.
  - rewrite σ_后继, 加后继, <- 后继_改写. apply IHα.
  - rewrite σ_极限, 加极限. split; constructor; intros n;
    eapply 弱序_极限_介入; rewrite IH; reflexivity.
Qed.

End 左加法不动点.

Section 左乘法不动点.
Variable ξ : 序数.
Variable ξ大于一 : [1] < ξ.

Definition π := (乘法 ξ)′.

Lemma π数为左乘法不动点 : ∀ α, ξ * (π α) ≃ π α.
Proof.
  apply 不动点枚举枚举之. apply 乘法为序数嵌入.
  eapply 强序_传递. apply 后继大于自身. auto.
Qed.

Lemma π_零 : π [0] ≃ [0].
Proof.
  split; constructor. induction n; simpl. constructor.
  replace ∅ with (ξ * [0]) at 2. apply 乘法_弱保序_右. apply IHn. apply 乘零.
Qed.

Lemma π_一 : π [1] ≃ ξ ^ ω.
Proof.
  intros. unfold ω. rewrite 极限次幂. split.
  - apply 后继不动点为之.
    + apply 乘法为序数嵌入. eapply 强序_传递. apply 后继大于自身. auto.
    + rewrite 乘极限. split; constructor; intros n.
      * apply 弱序_极限_介入 with (S n). simpl. rewrite 后继次幂. apply 乘法有限结合律.
      * apply 弱序_极限_介入 with n. apply 乘法_弱放大_左. auto.
    + apply 强序_极限_介入 with 0. rewrite 零次幂. apply 小于等于即小于后继.
      rewrite π_零. reflexivity.
  - constructor. induction n.
    + rewrite 零次幂. apply 弱序_极限_介入 with 0. simpl.
      rewrite <- 后继_弱保序. rewrite π_零. reflexivity.
    + simpl. rewrite 后继次幂, <- π数为左乘法不动点, <- 乘法有限结合律.
      apply 乘法_弱保序_右. apply IHn.
Qed.

Lemma π_后继 : ∀ α, π α⁺ ≃ π α + π [1].
Proof.
  intros. split.
  - unfold π at 1. rewrite 不动点枚举_后继. apply 后继不动点为之.
    + apply 乘法为序数嵌入. eapply 强序_传递. apply 后继大于自身. auto.
    + rewrite 乘法分配律, (加法_改写_左 (π α)), (加法_改写_右 (π [1])). reflexivity. 1-2: apply π数为左乘法不动点.
    + apply 加法_强放大_右. apply 小于即后继小于等于. rewrite π_一.
      apply 弱序_极限_介入 with 0. reflexivity.
  - constructor. intros n. apply 弱序_传递 with (π α + ξ ^ [n]). apply 加法_弱保序_右.
    + induction n; simpl.
      * rewrite 零次幂. simpl. rewrite <- 后继_弱保序. rewrite π_零. reflexivity.
      * rewrite 后继次幂, <- 乘法有限结合律. apply 乘法_弱保序_右. apply IHn.
    + induction n; simpl.
      * rewrite 零次幂, 加一. apply 小于即后继小于等于.
        apply 不动点枚举在后继处递增. apply 乘法为序数嵌入.
        eapply 强序_传递. apply 后继大于自身. auto.
      * rewrite 后继次幂, <- (π数为左乘法不动点 α⁺), (加法_改写_左 (ξ * π α)), (加法_改写_右 (ξ * ξ ^ [n])).
        rewrite <- 乘法分配律. apply 乘法_弱保序_右. apply IHn.
        rewrite 乘法有限结合律. reflexivity. rewrite π数为左乘法不动点. reflexivity.
Qed.

Lemma π_极限 : ∀ f, π (lim f) ≃ lim (λ n, π (f n)).
Proof. easy. Qed.

Theorem π表达式 : ∀ α, π α ≃ ξ ^ ω * α.
Proof.
  induction α as [| |f IH].
  - rewrite 乘零. apply π_零.
  - rewrite π_后继, 乘后继, 加法_改写_左, 加法_改写_右. reflexivity. apply π_一. apply IHα.
  - rewrite π_极限, 乘极限. split; constructor; intros n;
    eapply 弱序_极限_介入; rewrite IH; reflexivity.
Qed.

End 左乘法不动点.
