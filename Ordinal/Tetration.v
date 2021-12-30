(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.WellFormed.
Require Import GOO.Ordinal.Operation.
Require Import GOO.Ordinal.Recursion.
Require Import GOO.Ordinal.Arithmetic.

Local Open Scope 序数符号域.

Definition 左迭代 α β := 递归 (幂运算 α) α β.
Notation "α ^^ᴸ β" := (左迭代 α β) (at level 25) : 序数符号域.

Lemma 左迭代零次 : ∀ α, α ^^ᴸ [0] = α.
Proof. easy. Qed.

Lemma 左迭代后继次 : ∀ α β, α ^^ᴸ β⁺ = α ^ (α ^^ᴸ β).
Proof. easy. Qed.

Lemma 左迭代极限次 : ∀ α f, α ^^ᴸ lim f = lim (λ n, α ^^ᴸ f n).
Proof. easy. Qed.

Lemma 左迭代_弱保序_右 : ∀ α, [1] < α → 弱保序 (左迭代 α).
Proof.
  intros α H1 β γ H. apply 递归_弱保序_右.
  intros. apply 幂运算_弱放大_左. apply H1.
  apply 幂运算_弱保序_右. apply 诉诸强序. apply H1. apply H.
Qed.

Lemma 左迭代在ω后继处不递增 : ∀ α, [1] < α → α ^^ᴸ ω⁺ ≃ α ^^ᴸ ω.
Proof.
  intros. unfold ω. rewrite 左迭代后继次, 左迭代极限次, 极限次幂.
  split; constructor; intros n.
  - apply 弱序_极限_介入 with (S n). simpl. rewrite 左迭代后继次. reflexivity.
  - eapply 弱序_极限_介入. apply 幂运算_弱放大_左. apply H.
Qed.

Theorem 左迭代在ω次之后不变 : ∀ α β, [1] < α → 良构 β → ω ≤ β → α ^^ᴸ β ≃ α ^^ᴸ ω.
Proof with auto.
  intros α β H1 WF Inf. induction β as [|β IH|f IH].
  - exfalso. apply 弱序_反转 in Inf...
  - split. 2: apply 左迭代_弱保序_右... apply 良构无穷序数后继 in Inf...
    rewrite <- 左迭代在ω后继处不递增, 左迭代后继次, 左迭代后继次...
    apply 幂运算_弱保序_右... rewrite IH... reflexivity.
  - destruct WF as [WF Inc]. unfold ω. rewrite 左迭代极限次, 左迭代极限次.
    split; constructor; intros n.
    + pose proof (良构对ω排中 (f n)) as []...
      * apply 良构有限序数有自然数表示 in H as [m H]...
        rewrite H. eapply 弱序_极限_介入. reflexivity.
      * rewrite IH... unfold ω. rewrite 左迭代极限次. constructor. intros m.
        apply 弱序_极限_介入 with (S m). apply 左迭代_弱保序_右... simpl...
    + pose proof (良构对ω排中 (f n)) as []...
      * apply 弱序_极限_介入 with n. apply 左迭代_弱保序_右... apply 递增序列弱放大...
      * apply 弱序_极限_介入 with n. rewrite IH... apply 左迭代_弱保序_右...
Qed.

Definition 右迭代 α β := 递归 (λ ξ, ξ ^ α) α β.
Notation "α ^^ᴿ β" := (右迭代 α β) (at level 25) : 序数符号域.

Lemma 右迭代零次 : ∀ α, α ^^ᴿ [0] = α.
Proof. easy. Qed.

Lemma 右迭代后继次 : ∀ α β, α ^^ᴿ β⁺ = (α ^^ᴿ β) ^ α.
Proof. easy. Qed.

Lemma 右迭代极限次 : ∀ α f, α ^^ᴿ lim f = lim (λ n, α ^^ᴿ f n).
Proof. easy. Qed.

Theorem 右迭代化简 : ∀ α β, α ≠ [0] → α ^^ᴿ β ≃ α ^ (α ^ β).
Proof.
  intros. induction β as [|β IH|f IH].
  - rewrite 右迭代零次, 零次幂, 一次幂. reflexivity.
  - rewrite 右迭代后继次, 后继次幂, 指数积运算律.
    apply 幂运算_改写_左. apply IH.
  - rewrite 右迭代极限次, 极限次幂, 极限次幂. split; constructor; intros n;
    eapply 弱序_极限_介入; rewrite IH; reflexivity.
Qed.

(* α ^ α ^ ... ^ α ^ τ *)
Definition 顶迭代 := λ α β τ, 递归 (幂运算 α) τ β.
Notation "α ^^ᵀ β" := (顶迭代 α β) (at level 25) : 序数符号域.

Theorem 顶迭代零次 : ∀ τ α, (α ^^ᵀ [0]) τ = τ.
Proof. easy. Qed.

Theorem 顶迭代后继次 : ∀ τ α β, (α ^^ᵀ β⁺) τ = α ^ (α ^^ᵀ β) τ.
Proof. easy. Qed.

Theorem 顶迭代极限次 : ∀ τ α f, (α ^^ᵀ (lim f)) τ = lim (λ n, (α ^^ᵀ (f n)) τ).
Proof. easy. Qed.

Theorem 顶迭代一次 : ∀ τ α, (α ^^ᵀ [1]) τ = α ^ τ.
Proof. easy. Qed.

Lemma 有限顶迭代小于左迭代 : ∀ α τ n, [1] < α → τ < α → (α ^^ᵀ [n]) τ < α ^^ᴸ [n].
Proof with auto.
  intros. induction n.
  - easy.
  - simpl. rewrite 顶迭代后继次, 左迭代后继次... apply 幂运算_强保序_右...
Qed.

Lemma 有限左迭代小于后继顶迭代 : ∀ α τ n, [1] < τ → τ < α → α ^^ᴸ [n] < (α ^^ᵀ [S n]) τ.
Proof with auto.
  intros. assert ([1] < α). eapply 强序_传递; eauto.
  induction n.
  - rewrite 顶迭代一次, 左迭代零次... apply 幂运算_强放大_右...
  - simpl. rewrite 顶迭代后继次, 左迭代后继次... apply 幂运算_强保序_右...
Qed.

Theorem 无穷顶迭代等于左迭代 : ∀ α τ, [1] < τ → τ < α → (α ^^ᵀ ω) τ ≃ α ^^ᴸ ω.
Proof with auto.
  intros. assert ([1] < α). eapply 强序_传递; eauto.
  unfold ω. rewrite 顶迭代极限次, 左迭代极限次.
  split; constructor; intros n.
  - eapply 弱序_极限_介入 with n. apply 诉诸强序. apply 有限顶迭代小于左迭代...
  - eapply 弱序_极限_介入 with (S n). apply 诉诸强序. apply 有限左迭代小于后继顶迭代...
Qed.
