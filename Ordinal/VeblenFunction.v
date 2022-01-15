(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.WellFormed.
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

Fact cantor_零 : ∀ α, cantor α ∅ = α⁺.
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
  split3.
  - intros α β H. rewrite cantor0, cantor0. apply 幂运算_弱保序_右; auto.
  - intros α β H. eapply 弱强传递. apply cantor0.
    eapply 强弱传递. 2: apply cantor0. apply 幂运算_强保序_右; auto.
  - intros α. apply 诉诸强等. auto.
Qed.

Module Import 二元.

Definition 极限复合 (F : 序数 → 序数 → 序数) g :=
  λ β, lim (λ n, F (g n) β).
Notation "F ∘ g" := (极限复合 F g) (format "F ∘ g", at level 9) : 序数域.

Fixpoint veblen f α :=
  match α with
  | ∅ => f
  | α⁺ => (veblen f α)′
  | lim g => 递归 (λ β, (veblen f)∘g β⁺) ((veblen f)∘g ∅)
  end.

Definition φ := veblen (cantor ∅).
Definition Γ := (λ α, φ α ∅)′.

Definition ε1 := Γ′.
Definition ζ1 := ε1′.
Definition η1 := ζ1′.

Definition φ1 := veblen Γ.
Definition Γ1 := (λ α, φ1 α ∅)′.

Definition ε2 := Γ1′.
Definition ζ2 := ε2′.
Definition η2 := ζ2′.

Definition φ2 := veblen Γ1.
Definition Γ2 := (λ α, φ2 α ∅)′.

Fact φ_零 : ∀ β, φ ∅ β ≃ ω ^ β.
Proof. intros. simpl. unfold φ, veblen. rewrite cantor0. easy. Qed.

Fact φ_后继 : ∀ α, φ α⁺ = (φ α)′.
Proof. reflexivity. Qed.

Fact φ_极限 : ∀ f, φ (lim f) = 递归 (λ β, φ∘f β⁺) (φ∘f ∅).
Proof. reflexivity. Qed.

Fact φ_极限_零 : ∀ f, φ (lim f) ∅ = φ∘f ∅.
Proof. reflexivity. Qed.

Fact φ_极限_后继 : ∀ f α, φ (lim f) α⁺ = φ∘f (φ (lim f) α)⁺.
Proof. reflexivity. Qed.

Fact φ_极限_极限 : ∀ f g, φ (lim f) (lim g) = lim (λ n, φ (lim f) (g n)).
Proof. reflexivity. Qed.

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

Lemma φ_n为序数嵌入 : ∀ n, 序数嵌入 (φ [n]).
Proof.
  induction n.
  - apply cantor0为序数嵌入.
  - simpl. apply 函数外延保序数嵌入 with (λ x, (φ [n])′ x).
    intros x. rewrite φ_后继. reflexivity. apply 不动点枚举为序数嵌入. apply IHn.
Qed.

Lemma φ_n在零处强放大 : ∀ n, 零处强放大 (φ [n]).
Proof.
  induction n.
  - apply 强序_改写_右 with [1].
    + simpl. auto.
    + rewrite φ_零, 零次幂. reflexivity.
  - simpl. apply 强序_改写_右 with ((φ [n])′ ∅).
    + apply 不动点枚举在零处强放大. apply IHn.
    + rewrite φ_后继. reflexivity.
Qed.

Lemma φ_n在良构后继处强放大 : ∀ n, 良构后继处强放大 (φ [n]).
Proof.
  induction n; intros α WFα.
  - apply 强序_改写_右 with (ω ^ α⁺).
    + apply 以ω为底的幂运算在后继处强放大. apply WFα.
    + rewrite φ_零; reflexivity.
  - simpl. apply 强序_改写_右 with ((φ [n])′ α⁺).
    + apply 不动点枚举在良构后继处强放大. apply φ_n为序数嵌入. apply IHn. apply WFα.
    + rewrite φ_后继; reflexivity.
Qed.

Theorem φ_ω_0 : ∀ m, φ ω ∅ ≃ lim (λ n, φ [n] [m]).
Proof.
  unfold ω. rewrite φ_极限_零.
  split; constructor; intros n.
  - apply 弱序_极限_介入 with n. destruct n; simpl.
    + rewrite φ_零, φ_零. apply 幂运算_弱保序_右. auto. constructor.
    + rewrite φ_后继. apply 不动点枚举为序数嵌入. 2: constructor. apply φ_n为序数嵌入.
  - apply 弱序_极限_介入 with (S n). simpl. rewrite φ_后继. apply 诉诸强序. apply 不动点飞升.
    apply φ_n为序数嵌入. apply φ_n在零处强放大. apply φ_n在良构后继处强放大.
Qed.

Lemma φf弱保序 : ∀ f, (∀ n, 序数嵌入 (φ (f n))) → 弱保序 φ∘f.
Proof.
  intros f Emb. constructor. intros n.
  apply 弱序_极限_介入 with n. apply Emb. apply H.
Qed.

Lemma φ_lim弱保序 : ∀ f, (∀ n, 序数嵌入 (φ (f n))) → 弱保序 (φ (lim f)).
Proof.
  intros f Emb α β H. rewrite φ_极限.
  apply 递归_弱保序_右. 3: apply H.
  - intros γ. apply 弱序_极限_介入 with 0.
    apply 弱序_后继_除去. apply 序数嵌入弱放大. apply Emb.
  - intros γ δ Hle. apply φf弱保序. apply Emb.
    apply 后继_弱保序 in Hle. apply Hle.
Qed.

Lemma φ_lim强保序 : ∀ f, (∀ n, 序数嵌入 (φ (f n))) → 强保序 (φ (lim f)).
Proof.
  intros f Emb α β H. rewrite φ_极限.
  apply 递归_强保序_右. 3: apply H.
  - intros γ. apply 强序_极限_介入 with 0.
    apply 小于即后继小于等于. apply 序数嵌入弱放大. apply Emb.
  - intros γ δ Hle. apply φf弱保序. apply Emb.
    apply 后继_弱保序 in Hle. apply Hle.
Qed.

Lemma φ_lim在极限处连续 : ∀ f, 极限处连续 (φ (lim f)).
Proof.
  intros. rewrite φ_极限_极限. split; constructor; intros n;
  apply 弱序_极限_介入 with n; reflexivity.
Qed.

Theorem φ_α为序数嵌入 : ∀ α, 序数嵌入 (φ α).
Proof.
  induction α as [|α IH|f IH].
  - apply cantor0为序数嵌入.
  - simpl. apply 函数外延保序数嵌入 with (λ x, (φ α)′ x).
    intros x. rewrite φ_后继. reflexivity. apply 不动点枚举为序数嵌入. apply IH.
  - split3. apply φ_lim弱保序. apply IH. apply φ_lim强保序. apply IH.
    apply φ_lim在极限处连续.
Qed.

End 二元.

Module Import 三元.

Definition 极限复合 (F : 序数 → 序数 → 序数 → 序数) g :=
  λ β γ, lim (λ n, F (g n) β γ).
Notation "F ∘∘ g" := (极限复合 F g) (format "F ∘∘ g", at level 9) : 序数域.

Fixpoint veblen f α :=
  match α with
  | ∅ => f
  | α⁺ => 二元.veblen (λ β, veblen f α β ∅)′
  | lim g => 二元.veblen (递归 (λ β, (veblen f)∘∘g β⁺ ∅) ((veblen f)∘∘g ∅ ∅))
  end.

Definition φ := veblen 二元.φ.

Fact φ_零 : φ ∅ = 二元.φ.
Proof. reflexivity. Qed.

Fact φ_后继_零 : ∀ α, φ α⁺ ∅ = (λ β, φ α β ∅)′.
Proof. reflexivity. Qed.

Fact φ_后继_后继 : ∀ α β, φ α⁺ β⁺ = (φ α⁺ β)′.
Proof. reflexivity. Qed.

Fact φ_后继_极限 : ∀ α g, φ α⁺ (lim g) = 递归 (λ γ, (φ α⁺)∘g γ⁺) ((φ α⁺)∘g ∅).
Proof. reflexivity. Qed.

Fact φ_极限_零 : ∀ f, φ (lim f) ∅ = 递归 (λ γ, φ∘∘f γ⁺ ∅) (φ∘∘f ∅ ∅).
Proof. reflexivity. Qed.

Fact φ_极限_零_零 : ∀ f, φ (lim f) ∅ ∅ = φ∘∘f ∅ ∅.
Proof. reflexivity. Qed.

Fact φ_极限_零_后继 : ∀ f γ, φ (lim f) ∅ γ⁺ = φ∘∘f (φ (lim f) ∅ γ)⁺ ∅.
Proof. reflexivity. Qed.

Fact φ_极限_零_极限 : ∀ f g, φ (lim f) ∅ (lim g) = lim (λ n, φ (lim f) ∅ (g n)).
Proof. reflexivity. Qed.

Fact φ_极限_后继 : ∀ f β, φ (lim f) β⁺ = (φ (lim f) β)′.
Proof. reflexivity. Qed.

Fact φ_极限_极限_零 : ∀ f g, φ (lim f) (lim g) ∅ = (φ (lim f))∘g ∅.
Proof. reflexivity. Qed.

Fact φ_极限_极限_后继 : ∀ f g γ, φ (lim f) (lim g) γ⁺ = (φ (lim f))∘g (φ (lim f) (lim g) γ)⁺.
Proof. reflexivity. Qed.

Fact φ_极限_极限_极限 : ∀ f g h, φ (lim f) (lim g) (lim h) = lim (λ n, φ (lim f) (lim g) (h n)).
Proof. reflexivity. Qed.

Remark φ_1_0_γ : ∀ γ, φ [1] [0] γ = 二元.Γ γ.
Proof. reflexivity. Qed.

Remark φ_1_1_γ : ∀ γ, φ [1] [1] γ = 二元.ε1 γ.
Proof. reflexivity. Qed.

Remark φ_1_2_γ : ∀ γ, φ [1] [2] γ = 二元.ζ1 γ.
Proof. reflexivity. Qed.

Remark φ_1_3_γ : ∀ γ, φ [1] [3] γ = 二元.η1 γ.
Proof. reflexivity. Qed.

Remark φ_1_ω_γ : ∀ γ, φ [1] ω γ = 二元.φ1 ω γ.
Proof. reflexivity. Qed.

Remark φ_2_0_γ : ∀ γ, φ [2] [0] γ = 二元.Γ1 γ.
Proof. reflexivity. Qed.

Remark φ_2_1_γ : ∀ γ, φ [2] [1] γ = 二元.ε2 γ.
Proof. reflexivity. Qed.

Remark φ_2_2_γ : ∀ γ, φ [2] [2] γ = 二元.ζ2 γ.
Proof. reflexivity. Qed.

Remark φ_2_3_γ : ∀ γ, φ [2] [3] γ = 二元.η2 γ.
Proof. reflexivity. Qed.

Remark φ_2_ω_γ : ∀ γ, φ [2] ω γ = 二元.φ2 ω γ.
Proof. reflexivity. Qed.

Remark φ_3_0_γ : ∀ γ, φ [3] [0] γ = 二元.Γ2 γ.
Proof. reflexivity. Qed.

End 三元.

Module 四元.

Definition 极限复合 (F : 序数 → 序数 → 序数 → 序数 → 序数) g :=
  λ β γ δ, lim (λ n, F (g n) β γ δ).
Notation "F ∘∘∘ g" := (极限复合 F g) (format "F ∘∘∘ g", at level 9) : 序数域.

Fixpoint veblen f α :=
  match α with
  | ∅ => f
  | α⁺ => 三元.veblen (二元.veblen (λ β, veblen f α β ∅ ∅)′)
  | lim g => 三元.veblen (二元.veblen (
    递归 (λ β, (veblen f)∘∘∘g β⁺ ∅ ∅) ((veblen f)∘∘∘g ∅ ∅ ∅)))
  end.

Definition φ := veblen 三元.φ.

Fact φ_零 : φ ∅ = 三元.φ.
Proof. reflexivity. Qed.

Fact φ_后继_零_零 : ∀ α, φ α⁺ ∅ ∅ = (λ β, φ α β ∅ ∅)′.
Proof. reflexivity. Qed.

Fact φ_α_零_后继 : ∀ α γ, φ α ∅ γ⁺ = (φ α ∅ γ)′.
Proof. destruct α; reflexivity. Qed.

Fact φ_α_后继_零 : ∀ α β, φ α β⁺ ∅ = (λ γ, φ α β γ ∅)′.
Proof. destruct α; reflexivity. Qed.

Fact φ_α_β_后继 : ∀ α β γ, φ α β γ⁺ = (φ α β γ)′.
Proof. destruct α; destruct β; reflexivity. Qed.

Fact φ_α_β_极限 : ∀ α β f, φ α β (lim f) = 递归 (λ δ, (φ α β)∘f δ⁺) ((φ α β)∘f ∅).
Proof. destruct α; destruct β; reflexivity. Qed.

Fact φ_α_β_极限_零 : ∀ α β f, φ α β (lim f) ∅ = (φ α β)∘f ∅.
Proof. destruct α; destruct β; reflexivity. Qed.

Fact φ_α_β_极限_后继 : ∀ α β f δ, φ α β (lim f) δ⁺ = (φ α β)∘f (φ α β (lim f) δ)⁺.
Proof. destruct α; destruct β; reflexivity. Qed.

Fact φ_α_β_极限_极限 : ∀ α β f g, φ α β (lim f) (lim g) = lim (λ n, φ α β (lim f) (g n)).
Proof. destruct α; destruct β; reflexivity. Qed.

Fact φ_α_极限_零 : ∀ α f, φ α (lim f) ∅ = 递归 (λ δ, (φ α)∘∘f δ⁺ ∅) ((φ α)∘∘f ∅ ∅).
Proof. destruct α; reflexivity. Qed.

Fact φ_α_极限_零_零 : ∀ α f, φ α (lim f) ∅ ∅ = (φ α)∘∘f ∅ ∅.
Proof. destruct α; reflexivity. Qed.

Fact φ_α_极限_零_后继 : ∀ α f δ, φ α (lim f) ∅ δ⁺ = (φ α)∘∘f (φ α (lim f) ∅ δ)⁺ ∅.
Proof. destruct α; reflexivity. Qed.

Fact φ_α_极限_零_极限 : ∀ α f g, φ α (lim f) ∅ (lim g) = lim (λ n, φ α (lim f) ∅ (g n)).
Proof. destruct α; reflexivity. Qed.

Fact φ_极限_零_零 : ∀ f, φ (lim f) ∅ ∅ = 递归 (λ δ, φ∘∘∘f δ⁺ ∅ ∅) (φ∘∘∘f ∅ ∅ ∅).
Proof. reflexivity. Qed.

Fact φ_极限_零_零_零 : ∀ f, φ (lim f) ∅ ∅ ∅ = φ∘∘∘f ∅ ∅ ∅.
Proof. reflexivity. Qed.

Fact φ_极限_零_零_后继 : ∀ f δ, φ (lim f) ∅ ∅ δ⁺ = φ∘∘∘f (φ (lim f) ∅ ∅ δ)⁺ ∅ ∅.
Proof. reflexivity. Qed.

Fact φ_极限_零_零_极限 : ∀ f g, φ (lim f) ∅ ∅ (lim g) = lim (λ n, φ (lim f) ∅ ∅ (g n)).
Proof. reflexivity. Qed.

Example φ_1_0_0_0 : φ [1] [0] [0] [0] = (λ α, 三元.φ α ∅ ∅)′ ∅.
Proof. reflexivity. Qed.

Example φ_1_0_0_1 : φ [1] [0] [0] [1] = Itω (λ α, 三元.φ α ∅ ∅) (φ [1] [0] [0] [0])⁺.
Proof. reflexivity. Qed.

Example φ_1_0_0_2 : φ [1] [0] [0] [2] = Itω (λ α, 三元.φ α ∅ ∅) (φ [1] [0] [0] [1])⁺.
Proof. reflexivity. Qed.

Example φ_1_0_0_ω : φ [1] [0] [0] ω = lim (λ n, φ [1] [0] [0] [n]).
Proof. reflexivity. Qed.

Example φ_1_0_0_φ_1_0_0_0 : φ [1] [0] [0] (φ [1] [0] [0] [0]) =
  lim (λ n, φ [1] [0] [0] (迭代 (λ α, 三元.φ α ∅ ∅) ∅ n)).
Proof. reflexivity. Qed.

Example φ_1_0_1_0 : φ [1] [0] [1] [0] = Itω (λ δ, φ [1] [0] [0] δ) ∅.
Proof. reflexivity. Qed.

Example φ_1_0_ω_0 : φ [1] [0] ω [0] = lim (λ n, φ [1] [0] [n] [0]).
Proof. reflexivity. Qed.

Example φ_1_1_0_0 : φ [1] [1] [0] [0] = Itω (λ γ, φ [1] [0] γ [0]) ∅.
Proof. reflexivity. Qed.

Example φ_2_0_0_0 : φ [2] [0] [0] [0] = Itω (λ β, φ [1] β [0] [0]) ∅.
Proof. reflexivity. Qed.

End 四元.
