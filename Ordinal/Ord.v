(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Export Coq.Unicode.Utf8_core.
Require Export Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Tactic Notation "split3" := split; [|split].

Declare Scope 序数域.
Delimit Scope 序数域 with ord.
Local Open Scope 序数域.

Inductive 序数 : Set :=
  | 零 : 序数
  | 后继 : 序数 → 序数
  | 极限 : (nat → 序数) → 序数.

Notation "∅" := 零.
Notation "α ⁺" := (后继 α) (format "α ⁺", at level 6) : 序数域.
Notation lim := 极限.

Fixpoint 前驱深度 α : Set :=
  match α with
  | ∅ => False
  | α⁺ => unit + 前驱深度 α
  | lim f => { n & 前驱深度 (f n) }
  end.

Reserved Infix "⇠" (at level 20).
Fixpoint 前驱 α : 前驱深度 α → 序数 :=
  match α with
  | ∅ => False_rect _
  | α⁺ => λ d, match d with
    | inl tt => α
    | inr d  => d ⇠ α
    end
  | lim f => λ d, match d with
    | existT _ n d => d ⇠ (f n)
    end
  end
where "d ⇠ α" := (前驱 α d) : 序数域.

Reserved Infix "≤" (at level 70).
Inductive 弱序 : 序数 → 序数 → Prop :=
  | 弱序_零 : ∀ β, ∅ ≤ β
  | 弱序_后继 : ∀ α β d, α ≤ d ⇠ β → α⁺ ≤ β
  | 弱序_极限 : ∀ f β, (∀ n, f n ≤ β) → lim f ≤ β
where "α ≤ β" := (弱序 α β) : 序数域.
Notation "α ≰ β" := (¬ 弱序 α β) (at level 70) : 序数域.

Definition 强序 α β := ∃ d, α ≤ d ⇠ β.
Notation "α < β" := (  强序 α β) : 序数域.
Notation "α ≮ β" := (¬ 强序 α β) (at level 70) : 序数域.

Definition 弱等 α β := α ≤ β ∧ β ≤ α.
Notation "α ≃ β" := (  弱等 α β) (no associativity, at level 75) : 序数域.
Notation "α ≄ β" := (¬ 弱等 α β) (no associativity, at level 75) : 序数域.

Lemma 序数等于其后继的1前驱 : ∀ α, α = (inl tt) ⇠ α⁺.
Proof. easy. Qed.

Lemma 弱序_前驱_除去 : ∀ α β (d : 前驱深度 β), α ≤ d ⇠ β → α ≤ β.
Proof.
  induction α as [|α IH|f IH]; intros β d H.
  - constructor.
  - econstructor. inversion_clear H. eapply IH. eassumption.
  - constructor. intros n. inversion_clear H. eapply IH. easy.
Qed.

Lemma 弱序_前驱_介入 : ∀ α β (d : 前驱深度 α), α ≤ β → d ⇠ α ≤ β.
Proof.
  intros α β d H. induction H as [|α β b H IH|f β H IH].
  - destruct d.
  - destruct d as [[]|]; eapply 弱序_前驱_除去. apply H. apply IH.
  - destruct d. apply IH.
Qed.

Lemma 弱序_后继_除去 : ∀ α β, α⁺ ≤ β → α ≤ β.
Proof.
  intros. rewrite (序数等于其后继的1前驱 α).
  apply 弱序_前驱_介入. easy.
Qed.

Lemma 弱序_后继_介入 : ∀ α β, α ≤ β → α ≤ β⁺.
Proof.
  induction α as [|α _|f IH]; intros β H.
  - constructor.
  - inversion_clear H. apply 弱序_后继 with (inr d). easy.
  - constructor. intros n. apply IH. inversion_clear H. easy.
Qed.

Lemma 弱序_极限_除去 : ∀ α f n, lim f ≤ α → f n ≤ α.
Proof. intros. inversion_clear H. easy. Qed.

Lemma 弱序_极限_介入 : ∀ α f n, α ≤ f n → α ≤ lim f.
Proof.
  induction α as [|α _|f IH]; intros g n H.
  - constructor.
  - inversion_clear H. apply 弱序_后继 with (existT _ n d). easy.
  - constructor. intros m. eapply IH. inversion_clear H. easy.
Qed.

Theorem 弱序_自反 : Reflexive 弱序.
Proof.
  intros α. induction α as [|α IH|f IH].
  - constructor.
  - apply 弱序_后继 with (inl tt). easy.
  - constructor. intros n. eapply 弱序_极限_介入. apply IH.
Qed.

Theorem 弱序_传递 : Transitive 弱序.
Proof.
  intros α β γ H1. revert γ.
  induction H1 as [|α β d H IH|f β H IH]; intros γ H2.
  - constructor.
  - induction H2 as [|β γ y H' _|f γ H' IH'].
    + destruct d.
    + apply 弱序_后继 with y. apply IH.
      destruct d as [[]|d]; simpl in *. easy.
      apply 弱序_前驱_介入. easy.
    + destruct d as [n d]; simpl in *. eapply IH'. apply H. apply IH.
  - constructor. intros n. apply IH. easy.
Qed.

Theorem 弱序_预序 : PreOrder 弱序.
Proof. split. apply 弱序_自反. apply 弱序_传递. Qed.
Global Existing Instance 弱序_预序.

Example 序列极限与起始无关 : ∀ f, f 0 ≤ f 1 → lim f ≃ lim (λ n, f (S n)).
Proof.
  intros. split; constructor.
  - destruct n.
    + apply 弱序_极限_介入 with 0. auto.
    + apply 弱序_极限_介入 with n. reflexivity.
  - destruct n.
    + apply 弱序_极限_介入 with 1. reflexivity.
    + apply 弱序_极限_介入 with (S (S n)). reflexivity.
Qed.

Lemma 弱等_自反 : Reflexive 弱等.
Proof. split; apply 弱序_自反. Qed.

Lemma 弱等_对称 : Symmetric 弱等.
Proof. split; apply H. Qed.

Lemma 弱等_传递 : Transitive 弱等.
Proof.
  intros α β γ H1 H2. destruct H1. destruct H2.
  split; eapply 弱序_传递; eassumption.
Qed.

Theorem 弱等_等价 : Equivalence 弱等.
Proof. split. apply 弱等_自反. apply 弱等_对称. apply 弱等_传递. Qed.
Global Existing Instance 弱等_等价.

Theorem 弱序_偏序 : PartialOrder 弱等 弱序.
Proof. easy. Qed.
Global Existing Instance 弱序_偏序.

Corollary 弱序_反对称 : Antisymmetric 序数 弱等 弱序.
Proof. apply partial_order_antisym. apply 弱序_偏序. Qed.

Theorem 后继_弱保序 : ∀ α β, α ≤ β ↔ α⁺ ≤ β⁺.
Proof.
  split; intros H.
  - apply 弱序_后继 with (inl tt). easy.
  - inversion_clear H. destruct d as [[]|d].
    easy. eapply 弱序_前驱_除去. apply H0.
Qed.

Theorem 后继_改写 : ∀ α β, α ≃ β ↔ α⁺ ≃ β⁺.
Proof. firstorder using 后继_弱保序. Qed.

(* 后继不小于等于零 *)
Lemma 非弱序_后继_零 : ∀ α, α⁺ ≰ ∅.
Proof. intros α H. inversion_clear H. destruct d. Qed.

(* 序数的后继不小于等于该序数 *)
Lemma 非弱序_后继_自身 : ∀ α, α⁺ ≰ α.
Proof.
  induction α as [|α IH|f IH]; intros H.
  - apply 非弱序_后继_零 with ∅. easy.
  - apply IH. apply 后继_弱保序. easy.
  - inversion_clear H. inversion_clear H0. destruct d as [n d].
    apply IH with n. apply 弱序_后继 with d. easy.
Qed.

Lemma 非弱序_反转_前驱 : ∀ α β d, α ≤ β → β ≰ d ⇠ α.
Proof.
  induction α as [|α IH|f IH]; intros β d H1 H2.
  - destruct d.
  - destruct d as [|d]. destruct u.
    + apply 非弱序_后继_自身 with α. apply 弱序_传递 with β; easy.
    + apply IH with β d. apply 弱序_后继_除去. easy. easy.
  - inversion_clear H1. destruct d as [n d]. eapply IH. easy. eassumption.
Qed.

Lemma 非弱序_自身_前驱 : ∀ α d, α ≰ d ⇠ α.
Proof. intros. apply 非弱序_反转_前驱, 弱序_自反. Qed.

Lemma 强序_反自反 : Irreflexive 强序.
Proof. intros α [d H]. eapply 非弱序_自身_前驱. eassumption. Qed.

Lemma 强序_传递 : Transitive 强序.
Proof.
  intros α β γ H1 H2. destruct H1 as [d1 H1]. destruct H2 as [d2 H2].
  exists d2. apply 弱序_传递 with β. apply 弱序_前驱_除去 with d1. easy. easy.
Qed.

Theorem 强序_拟序 : StrictOrder 强序.
Proof. split. apply 强序_反自反. apply 强序_传递. Qed.
Global Existing Instance 强序_拟序.

Corollary 强序_非对称 : Asymmetric 强序.
Proof. apply StrictOrder_Asymmetric. apply 强序_拟序. Qed.

Fact 诉诸强序 : ∀ α β, α < β → α ≤ β.
Proof. intros α β [d H]. apply 弱序_前驱_除去 with d. easy. Qed.
Global Hint Resolve 诉诸强序 : core.

Fact 强序_反转 : ∀ α β, α < β → β ≰ α.
Proof. intros * [d H1] H2. eapply 非弱序_反转_前驱; eassumption. Qed.

Fact 弱序_反转 : ∀ α β, α ≤ β → β ≮ α.
Proof. intros * H1 [d H2]. apply 非弱序_反转_前驱 with α β d; easy. Qed.

Fact 后继大于零 : ∀ α, ∅ < α⁺.
Proof. intros. exists (inl tt). constructor. Qed.
Global Hint Resolve 后继大于零 : core.

Fact 后继大于自身 : ∀ α, α < α⁺.
Proof. intros. exists (inl tt). apply 弱序_自反. Qed.
Global Hint Resolve 后继大于自身 : core.

Fact 后继大于等于自身 : ∀ α, α ≤ α⁺.
Proof. intros. apply 诉诸强序. auto. Qed.
Global Hint Resolve 后继大于等于自身 : core.

Theorem 小于即后继小于等于 : ∀ α β, α < β ↔ α⁺ ≤ β.
Proof.
  split.
  - intros [d H]. apply 弱序_后继 with d. easy.
  - intros. inversion_clear H. exists d. easy.
Qed.

Theorem 小于等于即小于后继 : ∀ α β, α ≤ β ↔ α < β⁺.
Proof.
  split.
  - intros H. exists (inl tt). easy.
  - intros [d H]. destruct d as [[]|d]. easy. simpl in H.
    eapply 弱序_前驱_除去. eassumption.
Qed.

Fact 序数不稠密 : ∀ α β, α < β → β < α⁺ → False.
Proof. intros α β H1 H2. apply 小于等于即小于后继 in H2. apply 弱序_反转 in H2. easy. Qed.

Theorem 后继_强保序 : ∀ α β, α < β ↔ α⁺ < β⁺.
Proof. intros. rewrite 小于即后继小于等于, 小于等于即小于后继. easy. Qed.

Lemma 强弱传递 : ∀ α β γ, α < β → β ≤ γ → α < γ.
Proof. intros. rewrite 小于即后继小于等于 in *. eapply 弱序_传递; eassumption. Qed.

Lemma 弱强传递 : ∀ α β γ, α ≤ β → β < γ → α < γ.
Proof.
  intros. rewrite 小于即后继小于等于 in *.
  apply 后继_弱保序 in H. eapply 弱序_传递; eassumption.
Qed.

Lemma 强序_极限_介入 : ∀ α f n, α < f n → α < lim f.
Proof.
  intros. apply 小于即后继小于等于. eapply 弱序_极限_介入.
  apply 小于即后继小于等于. apply H.
Qed.

Lemma 强序_极限_除去 : ∀ α f n, lim f < α → f n < α.
Proof. intros. destruct H as [d H]. inversion_clear H. exists d. apply H0. Qed.

Lemma 弱序_前驱后继_自身 : ∀ α d, (d ⇠ α)⁺ ≤ α.
Proof.
  intros. induction α as [|α IH|f IH].
  - destruct d.
  - destruct d as [|d].
    + destruct u. simpl. reflexivity.
    + simpl. apply 弱序_传递 with α. apply IH. easy.
  - econstructor. reflexivity.
Qed.

Reserved Notation "[ n ]".
Fixpoint 有限序数 n :=
  match n with
  | O => ∅
  | S m => [m]⁺
  end
where "[ n ]" := (有限序数 n) : 序数域.

Definition ω := lim 有限序数.

Fact 自然数嵌入是单射 : ∀ n m : nat, [n] = [m] → n = m.
Proof.
  induction n; destruct m; simpl; intros H.
  easy. easy. easy. f_equal. apply IHn. injection H. easy.
Qed.

Lemma ω大于零 : ∅ < ω.
Proof. exists (existT _ 1 (inl tt)). constructor. Qed.
Global Hint Resolve ω大于零 : core.

Lemma 有限序数后继 : ∀ α, α < ω → α⁺ < ω.
Proof.
  intros. destruct H as [d H]. destruct d as [n d]. simpl in H.
  exists (existT _ (S n) (inl tt)). simpl in *.
  apply 后继_弱保序 in H. eapply 弱序_传递. apply H. apply 弱序_前驱后继_自身.
Qed.

Theorem ω大于有限序数 : ∀ n : nat, [n] < ω.
Proof.
  induction n.
  - apply ω大于零.
  - simpl. apply 有限序数后继. apply IHn.
Qed.
Global Hint Resolve ω大于有限序数 : core.
