(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.WellFormed.

Local Open Scope 序数域.

Notation 保良构 F := (∀ α, 良构 α → 良构 (F α)).

Notation 零处强放大 F := (∅ < F ∅).
Notation 良构后继处强放大 F := (∀ α, 良构 α → α⁺ < F α⁺).

Notation 弱放大 F := (∀ α, α ≤ F α).
Notation 强放大 F := (∀ α, α < F α).

Notation 弱保序 F := (∀ α β, α ≤ β → F α ≤ F β).
Notation 强保序 F := (∀ α β, α < β → F α < F β).

Notation 后继处递增 F := (∀ α, F α < F α⁺).
Notation 前驱处递增 F := (∀ α d, F (d ⇠ α)⁺ ≤ F α).
Notation 极限处连续 F := (∀ f, F (lim f) = lim (λ n, F (f n))).

(* normal function *)
Definition 序数嵌入 F := 弱保序 F ∧ 强保序 F ∧ 极限处连续 F.

Lemma 强放大弱放大 : ∀ F, 强放大 F → 弱放大 F.
Proof. intros. apply 诉诸强序. apply H. Qed.

Lemma 强保序在后继处递增 : ∀ F, 强保序 F → 后继处递增 F.
Proof. firstorder. Qed.

Lemma 序数嵌入弱放大 : ∀ F, 序数嵌入 F → 弱放大 F.
Proof.
  intros F [_ [OP Conti]]. induction α as [|α IH|f IH].
  - constructor.
  - apply 后继_弱保序 in IH. eapply 弱序_传递. apply IH.
    apply 小于即后继小于等于. apply OP. easy.
  - rewrite Conti. constructor. intros n. eapply 弱序_极限_介入. apply IH.
Qed.
