(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import Coq.Arith.PeanoNat.
Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.WellFormed.
Require Import GOO.Ordinal.Operation.
Require Import GOO.Ordinal.Recursion.

Local Open Scope 序数域.

Declare Scope 序数算术域.
Delimit Scope 序数算术域 with oa.
Local Open Scope 序数算术域.

Definition 加法 α β := 递归 后继 α β.
Notation "α + β" := (加法 α β) : 序数算术域.

Definition 乘法 α β := 递归 (λ ξ, ξ + α) [0] β.
Notation "α * β" := (乘法 α β) : 序数算术域.

Definition 幂运算 α β := 递归 (λ ξ, ξ * α) [1] β.
Notation "α ^ β" := (幂运算 α β) : 序数算术域.

Lemma 加零 : ∀ α, α + [0] = α.
Proof. easy. Qed.

Lemma 加后继 : ∀ α β, α + β⁺ = (α + β)⁺.
Proof. easy. Qed.

Lemma 加极限 : ∀ α f, α + lim f = lim (λ n, α + f n).
Proof. easy. Qed.

Lemma 加一 : ∀ α, α + [1] = α⁺.
Proof. easy. Qed.

Lemma 加于零 : ∀ α, [0] + α ≃ α.
Proof.
  induction α as [| |f IH]. reflexivity.
  - rewrite 加后继, <- 后继_改写, IHα. reflexivity.
  - rewrite 加极限. split; constructor; intros n;
    apply 弱序_极限_介入 with n; rewrite IH; reflexivity.
Qed.

Theorem 有限加法等效 : ∀ n m : nat, [n] + [m] = [n + m].
Proof.
  intros n. induction m.
  - rewrite 加零, <- plus_n_O. reflexivity.
  - simpl. rewrite 加后继, <- plus_n_Sm, IHm. reflexivity.
Qed.

Corollary 有限加于一 : ∀ α, 良构 α → α < ω → [1] + α = α⁺.
Proof.
  intros α WF Fin.
  pose proof (良构有限序数有自然数表示 α WF Fin) as [n H]. subst.
  rewrite 有限加法等效. reflexivity.
Qed.

Example 一加一等于二 : [1] + [1] = [2].
Proof. easy. Qed.

Example 一加ω弱等于ω : [1] + ω ≃ ω.
Proof.
  unfold ω. rewrite 加极限. split; constructor; intros n.
  - apply 弱序_极限_介入 with (S n). rewrite 有限加法等效. reflexivity.
  - apply 弱序_极限_介入 with n. rewrite 有限加法等效. simpl. easy.
Qed.

Example ω加一等于ω的后继 : ω + [1] = ω⁺.
Proof. easy. Qed.

Example ω小于ω2 : ω < ω + ω.
Proof. unfold 加法. simpl. eapply 强序_极限_介入 with 1. simpl. easy. Qed.

Lemma 乘零 : ∀ α, α * [0] = [0].
Proof. easy. Qed.

Lemma 乘后继 : ∀ α β, α * β⁺ = α * β + α.
Proof. easy. Qed.

Lemma 乘极限 : ∀ α f, α * lim f = lim (λ n, α * f n).
Proof. easy. Qed.

Lemma 乘一 : ∀ α, α * [1] ≃ α.
Proof. intros. simpl. rewrite 乘后继, 乘零, 加于零. reflexivity. Qed.

Lemma 乘于零 : ∀ α, [0] * α ≃ [0].
Proof.
  induction α as [| |f IH]. reflexivity.
  - rewrite 乘后继, 加零, IHα. reflexivity.
  - rewrite 乘极限. split; constructor. intros n. apply IH.
Qed.

Lemma 乘于一 : ∀ α, [1] * α ≃ α.
Proof.
  induction α as [| |f IH]. reflexivity.
  - rewrite 乘后继, 加一, <- 后继_改写, IHα. reflexivity.
  - rewrite 乘极限. split; constructor; intros n.
    + rewrite IH. easy.
    + rewrite <- IH. apply 弱序_极限_介入 with n. reflexivity.
Qed.

Theorem 有限乘法等效 : ∀ n m : nat, [n] * [m] = [n * m].
Proof.
  intros n. induction m.
  - rewrite 乘零, <- mult_n_O. reflexivity.
  - simpl. rewrite 乘后继, <- mult_n_Sm, IHm, 有限加法等效. reflexivity.
Qed.

Lemma 零次幂 : ∀ α, α ^ [0] = [1].
Proof. easy. Qed.

Lemma 后继次幂 : ∀ α β, α ^ β⁺ = α ^ β * α.
Proof. easy. Qed.

Lemma 极限次幂 : ∀ α f, α ^ lim f = lim (λ n, α ^ f n).
Proof. easy. Qed.

Lemma 一次幂 : ∀ α, α ^ [1] ≃ α.
Proof. intros. simpl. rewrite 后继次幂, 零次幂, 乘于一. reflexivity. Qed.

Lemma 零的后继次幂 : ∀ α, [0] ^ α⁺ ≃ [0].
Proof. intros α. rewrite 后继次幂, 乘零. reflexivity. Qed.

Lemma 一的幂 : ∀ α, [1] ^ α ≃ [1].
Proof.
  induction α as [| |f IH].
  - rewrite 零次幂. reflexivity.
  - rewrite 后继次幂, 乘一, IHα. reflexivity.
  - rewrite 极限次幂. split.
    + constructor. intros n. rewrite IH. reflexivity.
    + apply 弱序_极限_介入 with 1. rewrite IH. reflexivity.
Qed.

Theorem 有限幂运算等效 : ∀ n m : nat, [n] ^ [m] = [n ^ m].
Proof.
  intros n. induction m.
  - rewrite 零次幂, Nat.pow_0_r. reflexivity.
  - simpl. rewrite 后继次幂, IHm, 有限乘法等效, Nat.mul_comm. reflexivity.
Qed.

Lemma 加法_弱放大_右 : ∀ α β, α ≤ α + β.
Proof. intros. apply 递归_弱放大_右. easy. Qed.

Lemma 加法_弱放大_左 : ∀ α β, α ≤ β + α.
Proof. intros. apply 递归_弱放大_左. easy. apply 后继_弱保序. Qed.

Lemma 加法_弱保序_右 : ∀ α, 弱保序 (加法 α).
Proof. intros. apply 递归_弱保序_右. easy. apply 后继_弱保序. easy. Qed.

Lemma 加法_弱保序_左 : ∀ α, 弱保序 (λ ξ, ξ + α).
Proof. intros α. apply 递归_弱保序_左. apply 后继_弱保序. Qed.

Lemma 加法_强保序_右 : ∀ α, 强保序 (加法 α).
Proof. intros. apply 递归_强保序_右; auto. apply 后继_弱保序. Qed.

Lemma 加法_强放大_右 : ∀ α β, [0] < β → α < α + β.
Proof. intros. apply 递归_强放大_右; auto. apply 后继_弱保序. Qed.

Lemma 加法_改写_右 : ∀ {α β} γ, β ≃ γ → α + β ≃ α + γ.
Proof. split; apply 加法_弱保序_右; rewrite H; reflexivity. Qed.

Lemma 加法_改写_左 : ∀ {α} β {γ}, α ≃ β → α + γ ≃ β + γ.
Proof. split; apply 加法_弱保序_左; rewrite H; reflexivity. Qed.

Lemma 乘法_弱保序_右 : ∀ α, 弱保序 (乘法 α).
Proof.
  intros. apply 递归_弱保序_右. intros. apply 加法_弱放大_右.
  apply 加法_弱保序_左. apply H.
Qed.

Lemma 乘法_弱放大_右 : ∀ α β, [1] ≤ β → α ≤ α * β.
Proof. intros. rewrite <- 乘一 at 1. apply 乘法_弱保序_右. apply H. Qed.

Lemma 乘法_弱保序_左 : ∀ α, 弱保序 (λ ξ, ξ * α).
Proof.
  intros α β γ Hlt. induction α as [| |f IH].
  - rewrite 乘零, 乘零. constructor.
  - rewrite 乘后继, 乘后继. apply 弱序_传递 with (β * α + γ).
    apply 加法_弱保序_右. apply Hlt. apply 加法_弱保序_左. apply IHα.
  - rewrite 乘极限, 乘极限. constructor. intros n.
    eapply 弱序_极限_介入. apply IH.
Qed.

Lemma 乘法_弱放大_左 : ∀ α β, [1] ≤ β → α ≤ β * α.
Proof. intros. rewrite <- 乘于一 at 1. apply 乘法_弱保序_左. apply H. Qed.

Lemma 乘法_强保序_右 : ∀ α, [0] < α → 强保序 (乘法 α).
Proof.
  intros α H0 β γ H. apply 递归_强保序_右.
  intros δ. apply 加法_强放大_右. easy. apply 加法_弱保序_左. easy.
Qed.

Lemma 乘法_强放大_右 : ∀ α β, [0] < α → [1] < β → α < α * β.
Proof.
  intros α β H0 H1. apply (乘法_强保序_右 α) in H1; auto.
  destruct H1 as [d H1]. rewrite 乘一 in H1. exists d. apply H1.
Qed.

Lemma 乘法_改写_右 : ∀ {α β} γ, β ≃ γ → α * β ≃ α * γ.
Proof. split; apply 乘法_弱保序_右; rewrite H; reflexivity. Qed.

Lemma 乘法_改写_左 : ∀ {α} β {γ}, α ≃ β → α * γ ≃ β * γ.
Proof. split; apply 乘法_弱保序_左; rewrite H; reflexivity. Qed.

Lemma 幂运算_弱保序_右 : ∀ α, [1] ≤ α → 弱保序 (幂运算 α).
Proof.
  intros α H1 β γ H. apply 递归_弱保序_右.
  intros. apply 乘法_弱放大_右. apply H1.
  apply 乘法_弱保序_左. apply H.
Qed.

Lemma 幂运算_弱放大_右 : ∀ α β, [1] ≤ α → [1] ≤ β → α ≤ α ^ β.
Proof. intros. rewrite <- 一次幂 at 1. apply 幂运算_弱保序_右; easy. Qed.

Lemma 幂运算_弱保序_左 : ∀ α, 弱保序 (λ ξ, ξ ^ α).
Proof.
  intros α β γ Hlt. induction α as [| |f IH].
  - rewrite 零次幂, 零次幂. reflexivity.
  - rewrite 后继次幂, 后继次幂. apply 弱序_传递 with (β ^ α * γ).
    apply 乘法_弱保序_右. apply Hlt. apply 乘法_弱保序_左. apply IHα.
  - rewrite 极限次幂, 极限次幂. constructor. intros n.
    eapply 弱序_极限_介入. apply IH.
Qed.

Lemma 乘二 : ∀ α, α * [2] ≃ α + α.
Proof. intros. simpl. rewrite 乘后继. apply 加法_改写_左. apply 乘一. Qed.

Lemma 幂运算_弱放大_左 : ∀ α β, [1] < β → α ≤ β ^ α.
Proof.
  intros. induction α as [| |f IH].
  - rewrite 零次幂. simpl. easy.
  - rewrite 后继次幂. apply 后继_弱保序 in IHα.
    apply 弱序_传递 with (β ^ α)⁺. easy.
    apply 弱序_传递 with (β ^ α + β ^ α).
    + rewrite <- 加一. apply 加法_弱保序_右. rewrite <- (零次幂 β).
      apply 幂运算_弱保序_右. apply 诉诸强序. apply H. constructor.
    + rewrite <- (乘二). apply 乘法_弱保序_右.
      apply 小于即后继小于等于. apply H.
  - constructor. intros n. apply 弱序_传递 with (β ^ f n). apply IH.
    unfold 幂运算. simpl. apply 弱序_极限_介入 with n. easy.
Qed.

Lemma 幂大于零 : ∀ α β, [1] ≤ α → [0] < α ^ β.
Proof.
  intros. apply 小于即后继小于等于. replace [0]⁺ with [1] by auto.
  rewrite <- (零次幂 α). apply 幂运算_弱保序_右. apply H. constructor.
Qed.

Lemma 幂运算_强保序_右 : ∀ α, [1] < α → 强保序 (幂运算 α).
Proof.
  intros α H1 β γ H. induction γ as [| |f IH].
  - destruct H as [d _]. destruct d.
  - apply 小于等于即小于后继 in H. apply (幂运算_弱保序_右 α) in H. 2: apply 诉诸强序; easy.
    apply 弱强传递 with (α ^ γ). apply H. rewrite 后继次幂.
    apply 乘法_强放大_右. apply 幂大于零. apply 诉诸强序. 1-2: apply H1.
  - rewrite 极限次幂. destruct H as [d H]. destruct d as [n d]. simpl in H.
    apply 强序_极限_介入 with n. apply IH. exists d. apply H.
Qed.

Lemma 幂运算_强放大_右 : ∀ α β, [1] < α → [1] < β → α < α ^ β.
Proof.
  intros α β Hα Hβ. apply (幂运算_强保序_右 α) in Hβ; auto.
  destruct Hβ as [d H]. rewrite 一次幂 in H. exists d. apply H.
Qed.

Lemma 幂运算_改写_右 : ∀ {α β} γ, [1] ≤ α → β ≃ γ → α ^ β ≃ α ^ γ.
Proof. split; apply 幂运算_弱保序_右; auto; rewrite H0; reflexivity. Qed.

Lemma 幂运算_改写_左 : ∀ {α} β {γ}, α ≃ β → α ^ γ ≃ β ^ γ.
Proof. split; apply 幂运算_弱保序_左; rewrite H; reflexivity. Qed.

Theorem 加法保良构 : ∀ α, 良构 α → 保良构 (加法 α).
Proof. intros α WFα β WFβ. apply 递归保良构; auto. apply 后继_弱保序. Qed.

Theorem 乘法保良构 : ∀ α, 良构 α → [0] < α → 保良构 (乘法 α).
Proof with auto.
  intros α WFα β WFβ. apply 递归保良构; auto.
  intros. apply 加法_强放大_右; auto.
  apply 加法_弱保序_左. intros. apply 加法保良构; auto. easy.
Qed.

Theorem 幂运算保良构 : ∀ α, 良构 α → [1] < α → 保良构 (幂运算 α).
Proof.
  intros α WFα H1 β WFβ. induction β as [| |f IH].
  - rewrite 零次幂. easy.
  - rewrite 后继次幂. apply 乘法保良构. apply IHβ. apply WFβ.
    apply 幂大于零. apply 小于即后继小于等于.
    apply 强序_传递 with [1]. simpl. easy. apply H1. apply WFα.
  - rewrite 极限次幂. split.
    + intros n. apply IH. apply WFβ.
    + intros n m Hnm. apply 幂运算_强保序_右. apply H1. apply WFβ. apply Hnm.
Qed.

Theorem 加法为序数嵌入 : ∀ α, 序数嵌入 (加法 α).
Proof. split3. apply 加法_弱保序_右. apply 加法_强保序_右. easy. Qed.

Theorem 乘法为序数嵌入 : ∀ α, [1] ≤ α → 序数嵌入 (乘法 α).
Proof.
  split3. apply 乘法_弱保序_右.
  apply 乘法_强保序_右. apply 小于即后继小于等于. easy. easy.
Qed.

Theorem 幂运算为序数嵌入 : ∀ α, [1] < α → 序数嵌入 (幂运算 α).
Proof.
  split3. apply 幂运算_弱保序_右. auto.
  apply 幂运算_强保序_右. easy. easy.
Qed.

Theorem 加法结合律 : ∀ α β γ, α + β + γ ≃ α + (β + γ).
Proof.
  intros. induction γ as [|γ IH|f IH].
  - rewrite 加零, 加零. reflexivity.
  - rewrite 加后继, 加后继, 加后继, <- 后继_改写, IH. reflexivity.
  - rewrite 加极限, 加极限, 加极限.
    split; constructor; intros n; eapply 弱序_极限_介入; apply IH.
Qed.

Theorem 乘法分配律 : ∀ α β γ, α * (β + γ) ≃ α * β + α * γ.
Proof.
  intros. induction γ as [|γ IH|f IH].
  - rewrite 加零, 乘零, 加零. reflexivity.
  - rewrite 乘后继, 加后继, 乘后继, <- 加法结合律. apply 加法_改写_左. apply IH.
  - rewrite 加极限, 乘极限, 乘极限, 加极限.
    split; constructor; intros n; eapply 弱序_极限_介入; apply IH.
Qed.

Theorem 乘法结合律 : ∀ α β γ, α * β * γ ≃ α * (β * γ).
Proof.
  intros. induction γ as [|γ IH|f IH].
  - rewrite 乘零, 乘零. reflexivity.
  - rewrite 乘后继, 乘后继, 乘法分配律. apply 加法_改写_左. apply IH.
  - rewrite 乘极限, 乘极限, 乘极限.
    split; constructor; intros n; eapply 弱序_极限_介入; apply IH.
Qed.

Theorem 指数和运算律 : ∀ α β γ, α ^ (β + γ) ≃ α ^ β * α ^ γ.
Proof.
  intros. induction γ as [|γ IH|f IH].
  - rewrite 加零, 零次幂, 乘一. reflexivity.
  - rewrite 加后继, 后继次幂, 后继次幂, <- 乘法结合律.
    apply 乘法_改写_左. apply IH.
  - rewrite 加极限, 极限次幂, 极限次幂, 乘极限.
    split; constructor; intros n; eapply 弱序_极限_介入; apply IH.
Qed.

Theorem 指数积运算律 : ∀ α β γ, α ^ (β * γ) ≃ (α ^ β) ^ γ.
Proof.
  intros. induction γ as [|γ IH|f IH].
  - rewrite 零次幂, 零次幂. reflexivity.
  - rewrite 后继次幂, 乘后继, 指数和运算律.
    apply 乘法_改写_左. apply IH.
  - rewrite 乘极限, 极限次幂, 极限次幂.
    split; constructor; intros n; eapply 弱序_极限_介入; apply IH.
Qed.

Lemma 无穷加于一 : ∀ α, 良构 α → ω ≤ α → [1] + α ≃ α.
Proof.
  intros α WF Inf. induction α as [|α IH|f IH].
  - exfalso. eapply 弱序_反转. apply Inf. apply ω大于零.
  - inversion_clear Inf. rewrite 加后继, <- 后继_改写. apply IH. apply WF.
    constructor. intros. specialize H with (S n). apply 后继_弱保序. apply H.
  - rewrite 加极限. split; constructor; intros.
    + pose proof (良构对ω排中 (f n)) as []. apply WF.
      * apply 弱序_传递 with ([1] + ω).
        apply 加法_弱保序_右. apply 诉诸强序. apply H.
        rewrite 一加ω弱等于ω. apply Inf.
      * apply 弱序_极限_介入 with n. rewrite IH. reflexivity. apply WF. apply H.
    + apply 弱序_极限_介入 with n. apply 加法_弱放大_左.
Qed.

Theorem 加法有限吸收律 : ∀ α n, 良构 α → ω ≤ α → [n] + α ≃ α.
Proof.
  intros α n WF Inf. induction n.
  - rewrite 加于零. reflexivity.
  - simpl. rewrite <- 加一, 加法结合律. rewrite <- IHn at 2.
    apply 加法_改写_右. apply 无穷加于一. apply WF. apply Inf.
Qed.

Theorem 加法有限结合律 : ∀ α n, α + α * [n] ≃ α * [n] + α.
Proof.
  intros α n. induction n.
  - rewrite 乘零, 加零, 加于零. reflexivity.
  - simpl. rewrite 乘后继, <- 加法结合律. apply 加法_改写_左. apply IHn.
Qed.

Theorem 乘法有限结合律 : ∀ α n, α * α ^ [n] ≃ α ^ [n] * α.
Proof.
  intros α n. induction n.
  - rewrite 零次幂, 乘一, 乘于一. reflexivity.
  - simpl. rewrite 后继次幂, <- 乘法结合律. apply 乘法_改写_左. apply IHn.
Qed.

Theorem ω幂对加法的吸收律 : ∀ α β, 良构 β → α < β → ω ^ α + ω ^ β ≃ ω ^ β.
Proof with auto.
  induction β as [|β IH|f IH]; intros WF H.
  - destruct H as [d _]. destruct d.
  - apply 小于等于即小于后继 in H. apply (幂运算_弱保序_右 ω) in H...
    rewrite 后继次幂. unfold ω at 3 5. rewrite 乘极限, 加极限.
    split; constructor; intros n.
    + apply 弱序_极限_介入 with (S n). simpl. rewrite 乘后继.
      apply 弱序_传递 with (ω ^ β + ω ^ β * [n]). apply 加法_弱保序_左...
      rewrite 加法有限结合律. reflexivity.
    + apply 弱序_极限_介入 with n. apply 加法_弱放大_左.
  - rewrite 极限次幂, 加极限. destruct WF as [WF Inc].
    apply 递增序列极限内有任意大的项 in H as [m H]...
    split; constructor; intros n.
    + pose proof (Nat.lt_trichotomy n m) as [|[]].
      * apply 弱序_传递 with (ω ^ α + ω ^ f m).
        apply 加法_弱保序_右. apply 幂运算_弱保序_右...
        apply 弱序_极限_介入 with m. apply IH...
      * apply 弱序_传递 with (ω ^ α + ω ^ f m).
        apply 加法_弱保序_右. apply 幂运算_弱保序_右... subst. reflexivity.
        apply 弱序_极限_介入 with m. apply IH...
      * apply 弱序_极限_介入 with n. apply IH... apply 强序_传递 with (f m)...
    + apply 弱序_极限_介入 with n. apply 加法_弱放大_左.
Qed.
