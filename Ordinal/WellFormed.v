(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.

Local Open Scope 序数符号域.

Notation 递增序列 f := (∀ n m, (n < m)%nat → f n < f m).

Lemma 递增序列弱放大 : ∀ f n, 递增序列 f → [n] ≤ f n.
Proof.
  intros. induction n. constructor. apply 后继_弱保序 in IHn.
  apply 弱序_传递 with (f n)⁺. apply IHn.
  apply 小于即后继小于等于. apply H. auto.
Qed.

Fixpoint 良构 α : Prop :=
  match α with
  | ∅ => True
  | α⁺ => 良构 α
  | lim f => (∀ n, 良构 (f n)) ∧ 递增序列 f
  end.

Lemma 有限序数良构 : ∀ n, 良构 [n].
Proof. induction n. easy. simpl. apply IHn. Qed.

Lemma 自然数序嵌入 : ∀ n m, (n < m)%nat → [n] < [m].
Proof.
  intros n m. revert n. induction m; intros n H. easy.
  inversion H. simpl. easy. apply 强序_传递 with [m]. apply IHm. apply H1. simpl. easy.
Qed.

Theorem ω_良构 : 良构 ω.
Proof. unfold ω. split. apply 有限序数良构. apply 自然数序嵌入. Qed.
Global Hint Resolve ω_良构 : core.

Lemma 序列_极限_介入 : ∀ f n, f n ≤ lim f.
Proof. intros. apply 弱序_极限_介入 with n. easy. Qed.
Global Hint Resolve 序列_极限_介入 : core.

Lemma 递增序列_极限_介入 : ∀ f n, 递增序列 f → f n < lim f.
Proof. intros. apply 强弱传递 with (f (S n)). apply H. auto. auto. Qed.

Lemma 递增序列存在非零取值 : ∀ f, 递增序列 f → ∃ n, f n ≠ [0].
Proof.
  intros f Inc. exists 1. intros C.
  assert (f 0 < f 1). apply Inc. auto.
  rewrite C in H. destruct H as [d _]. destruct d.
Qed.

Lemma 递增序列极限大于等于ω : ∀ f, 递增序列 f → ω ≤ lim f.
Proof.
  intros. constructor. intros n.
  apply 弱序_极限_介入 with n. apply 递增序列弱放大. apply H.
Qed.

Lemma 递增序列极限内有任意大的项 : ∀ α f, 递增序列 f → α < lim f → ∃ n, α < f n.
Proof with auto.
  intros α f Inc H. induction α as [|α IH|g IH].
  - exists 1. apply 弱强传递 with (f 0). constructor. apply Inc. auto.
  - destruct IH as [n Hn]. apply 强序_传递 with α⁺...
    exists (S n). apply 弱强传递 with (f n)... apply 小于即后继小于等于...
  - destruct H as [d H]. destruct d as [n d]. simpl in H.
    inversion_clear H. exists n. apply 弱强传递 with (d ⇠ f n).
    constructor. apply H0. exists d. reflexivity.
Qed.

Lemma 良构非零则大于零 : ∀ α, 良构 α → α ≠ [0] → [0] < α.
Proof.
  intros. induction α as [| |f IH]. exfalso. easy. easy.
  destruct H as [WF Inc]. apply 递增序列存在非零取值 in Inc as [n H].
  apply 强序_极限_介入 with n. apply IH. apply WF. apply H.
Qed.

Theorem 良构对零排中 : ∀ α, 良构 α → α = [0] ∨ [0] < α.
Proof.
  intros. destruct α as [| |f]. left. easy. right. easy.
  right. destruct H as [WF Inc]. apply 递增序列存在非零取值 in Inc as [n H].
  apply 强序_极限_介入 with n. apply 良构非零则大于零. apply WF. apply H.
Qed.

Lemma 小于等于零则弱等于零 : ∀ α, α ≤ ∅ → α ≃ ∅.
Proof.
  intros. destruct α as [| |f]. easy.
  - exfalso. apply 非弱序_后继_零 with α. easy.
  - split. easy. constructor.
Qed.

Lemma 良构弱等于零则等于零 : ∀ α, 良构 α → α ≃ [0] → α = [0].
Proof.
  intros α WF [H _]. destruct α as [| |f]. easy.
  - exfalso. eapply 非弱序_后继_零. apply H.
  - exfalso. destruct WF as [WF Inc].
    apply 递增序列存在非零取值 in Inc as [n H0].
    apply 良构非零则大于零 in H0; auto. apply 强序_反转 in H0.
    apply H0. apply 弱序_极限_除去. apply H.
Qed.

Theorem 良构小于等于零则等于零 : ∀ α, 良构 α → α ≤ ∅ → α = [0].
Proof. intros. apply 良构弱等于零则等于零; auto. apply 小于等于零则弱等于零; auto. Qed.

Theorem 良构对ω排中 : ∀ α, 良构 α → α < ω ∨ ω ≤ α.
Proof.
  intros α WF. induction α as [|α IH|f IH].
  - left. apply ω大于零.
  - simpl in WF. pose proof (IH WF) as [].
    + left. apply 有限序数后继. easy.
    + right. apply 弱序_传递 with α; easy.
  - right. apply 递增序列极限大于等于ω. apply WF.
Qed.

Corollary 良构无穷序数后继 : ∀ α, 良构 α → ω ≤ α⁺ → ω ≤ α.
Proof with auto.
  intros α WF Inf. pose proof (良构对ω排中 α) as []...
  exfalso. apply 弱序_反转 in Inf. apply Inf. apply 有限序数后继...
Qed.

Theorem 良构有限序数有自然数表示 : ∀ α, 良构 α → α < ω → ∃ n, α = [n].
Proof with auto.
  intros α WF Fin. induction α as [|α IH|f IH].
  - exists 0...
  - assert (Hn: ∃ n, α = [n]). apply IH... apply 强序_传递 with α⁺...
    destruct Hn as [n Hn]. exists (S n). rewrite Hn...
  - exfalso. eapply 强序_反转. apply Fin. apply 递增序列极限大于等于ω. apply WF.
Qed.
