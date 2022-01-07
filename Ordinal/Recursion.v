(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.Operation.
Require Import GOO.Ordinal.WellFormed.

Local Open Scope 序数域.

Fixpoint 递归 F α₀ α :=
  match α with
  | ∅ => α₀
  | α⁺ => F (递归 F α₀ α)
  | lim f => lim (λ n, 递归 F α₀ (f n))
  end.

Lemma 递归_弱放大_右 : ∀ F α, 弱放大 F → 弱放大 (λ ξ, 递归 F ξ α).
Proof.
  intros * NDecs β. induction α as [|α IH|f IH].
  - simpl. reflexivity.
  - simpl. apply 弱序_传递 with (递归 F β α). apply IH. apply NDecs.
  - apply 弱序_传递 with (递归 F β (f 0)). apply IH.
    simpl. apply 弱序_极限_介入 with 0. reflexivity.
Qed.

Lemma 递归_弱放大_左 : ∀ F α, 强放大 F → 弱保序 F → 弱放大 (递归 F α).
Proof.
  intros * Asc OP β. induction β as [|β IH|f IH].
  - simpl. constructor.
  - simpl. apply 后继_弱保序 in IH. eapply 弱序_传递. apply IH.
    apply 小于即后继小于等于. apply Asc.
  - simpl. constructor. intros n. apply 弱序_极限_介入 with n. apply IH.
Qed.

Lemma 递归前驱处递增 : ∀ F α, 弱放大 F → 前驱处递增 (递归 F α).
Proof.
  intros * Asc β d. induction β as [|β IH|f IH].
  - destruct d.
  - destruct d as [|d]. destruct u.
    + reflexivity.
    + simpl. apply 弱序_传递 with (递归 F α β). apply IH. apply Asc.
  - destruct d as [n d]. simpl.
    apply 弱序_传递 with (递归 F α (f n)). apply IH.
    apply 弱序_极限_介入 with n. reflexivity.
Qed.

Lemma 递归_弱保序_右 : ∀ F α, 弱放大 F → 弱保序 F → 弱保序 (递归 F α).
Proof.
  intros F α Asc OP β γ H. induction H as [|β γ d|f γ _].
  - simpl. apply 递归_弱放大_右. apply Asc.
  - simpl. apply OP in IH弱序.
    apply 弱序_传递 with (递归 F α (d ⇠ γ)⁺). apply IH弱序.
    apply 递归前驱处递增. apply Asc.
  - simpl. constructor. apply H.
Qed.

Lemma 递归_弱保序_左 : ∀ F α, 弱保序 F → 弱保序 (λ ξ, (递归 F ξ α)).
Proof.
  intros F α OP β γ H. simpl. induction α as [| |f IH].
  - simpl. easy.
  - simpl. apply OP. apply IHα.
  - simpl. constructor. intros n. apply 弱序_极限_介入 with n. apply IH.
Qed.

Lemma 递归_强保序_右 : ∀ F α, 强放大 F → 弱保序 F → 强保序 (递归 F α).
Proof with auto.
  intros F α Asc OP β γ H.
  pose proof (强放大弱放大 F Asc) as WAsc.
  destruct γ as [| |f].
  - destruct H as [d _]. destruct d.
  - apply 小于等于即小于后继 in H.
    apply 弱强传递 with (递归 F α γ). apply 递归_弱保序_右... apply Asc.
  - destruct H as [d H]. destruct d as [n d].
    simpl in H. apply (递归_弱保序_右 F α) in H...
    apply 强弱传递 with (递归 F α (d ⇠ f n)⁺).
    apply 弱强传递 with (递归 F α (d ⇠ f n))... simpl. apply Asc.
    apply 弱序_传递 with (递归 F α (f n)). apply 递归前驱处递增... apply 递归_弱保序_右...
Qed.

Lemma 递归_强放大_右 : ∀ F α, 强放大 F → 弱保序 F → [0] < α → 强放大 (λ ξ, 递归 F ξ α).
Proof with auto.
  intros F α Asc OP H β.
  pose proof (强放大弱放大 F Asc) as WAsc.
  induction α as [|α IH|f IH].
  - destruct H as [d _]. destruct d.
  - apply 弱强传递 with (递归 F β α). apply 递归_弱放大_右... apply 递归_强保序_右...
  - simpl. destruct H as [d H]. destruct d as [n d].
    apply 强序_极限_介入 with n. apply IH. exists d. constructor.
Qed.

Lemma 递归保良构 : ∀ F α, 强放大 F → 弱保序 F → 保良构 F → 良构 α → 保良构 (递归 F α).
Proof.
  intros * Asc OP WF WFα β WFβ. induction β as [| |f IH].
  - simpl. apply WFα.
  - simpl. apply WF. apply IHβ. apply WFβ.
  - simpl. split.
    + intros n. apply IH. apply WFβ.
    + intros n m Hnm. apply 递归_强保序_右. apply Asc. apply OP.
      apply WFβ. apply Hnm.
Qed.
