(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.WellFormed.
Require Import GOO.Ordinal.Operation.
Require Import GOO.Ordinal.Recursion.
Require Import GOO.Ordinal.Arithmetic.
Require Import GOO.Ordinal.Tetration.
Require Import GOO.Ordinal.Iteration.

Local Open Scope 序数域.
Local Open Scope 序数算术域.

Definition ε := (幂运算 ω)′.

Lemma ε为序数嵌入 : 序数嵌入 ε.
Proof. apply 不动点枚举为序数嵌入. apply 幂运算为序数嵌入. auto. Qed.

Lemma ε数为不动点 : ∀ α, ω ^ (ε α) ≃ ε α.
Proof. apply 不动点枚举枚举之. apply 幂运算为序数嵌入. auto. Qed.

Theorem ε_零 : ε [0] ≃ ω ^^ᴸ ω.
Proof with auto.
  split; constructor.
  - induction n; simpl.
    + constructor.
    + rewrite <- 左迭代在ω后继处不递增, 左迭代后继次... apply 幂运算_弱保序_右...
  - induction n; simpl.
    + constructor. intros n. apply 弱序_极限_介入 with 2. simpl. rewrite 零次幂, 一次幂...
    + rewrite <- ε数为不动点. apply 幂运算_弱保序_右...
Qed.

Theorem ε_后继_ω塔 : ∀ α, ε α⁺ ≃ (ω ^^ᵀ ω) (ε α)⁺.
Proof.
  intros. unfold ε, ω. rewrite 不动点枚举_后继, 顶迭代极限次.
  rewrite 无穷迭代弱等于无穷递归. unfold ω. reflexivity.
Qed.

Theorem ε_极限 : ∀ f, ε (lim f) ≃ lim (λ n, ε (f n)).
Proof. easy. Qed.

Lemma 以ω为底的幂运算在零处强放大 : 零处强放大 (幂运算 ω).
Proof. rewrite 零次幂. simpl. easy. Qed.

Lemma 以ω为底的幂运算在后继处强放大 : 良构后继处强放大 (幂运算 ω).
Proof with auto.
  intros α WFα. destruct (良构对零排中 α)...
  - rewrite H. apply 小于即后继小于等于. rewrite 一次幂.
    apply 小于即后继小于等于. apply 有限序数后继...
  - rewrite 后继次幂, <- 加一. apply 强弱传递 with (α * ω).
    + apply 弱强传递 with (α * [2]).
      * rewrite 乘二. apply 加法_弱保序_右. simpl. apply 小于即后继小于等于...
      * apply 乘法_强保序_右...
    + apply 乘法_弱保序_左. apply 幂运算_弱放大_左...
Qed.

Theorem ε保良构 : 保良构 ε.
Proof with auto.
  intros. apply 不动点枚举保良构...
  - apply 幂运算为序数嵌入...
  - apply 以ω为底的幂运算在零处强放大.
  - apply 以ω为底的幂运算在后继处强放大.
  - apply 幂运算保良构...
Qed.

Lemma ε在零处强放大 : 零处强放大 ε.
Proof. apply 不动点枚举在零处强放大. apply 以ω为底的幂运算在零处强放大. Qed.

Lemma ε在良构后继处强放大 : 良构后继处强放大 ε.
Proof. 
  apply 不动点枚举在良构后继处强放大. apply 幂运算为序数嵌入. auto.
  apply 以ω为底的幂运算在后继处强放大.
Qed.

Lemma ε数大于一 : ∀ α, [1] < ε α.
Proof.
  intros. apply 强弱传递 with (ε [0]).
  - apply 小于即后继小于等于. rewrite ε_零. apply 弱序_极限_介入 with 0. simpl.
    apply 弱序_极限_介入 with 2. reflexivity.
  - apply ε为序数嵌入. constructor.
Qed.
Local Hint Immediate ε数大于一 : core. 

(* ε'顶ω塔 := 以ε数的后继为顶的ω塔 *)

Fact ε'顶ω塔0层 : ∀ α, (ω ^^ᵀ [0]) (ε α)⁺ ≃ (ε α)⁺.
Proof. easy. Qed.

Fact ε'顶ω塔1层 : ∀ α, (ω ^^ᵀ [1]) (ε α)⁺ ≃ ε α * ω.
Proof.
  intros. rewrite 顶迭代一次, 后继次幂.
  apply 乘法_改写_左. apply ε数为不动点.
Qed.

Fact ε'顶ω塔2层 : ∀ α, (ω ^^ᵀ [2]) (ε α)⁺ ≃ ε α ^ ω.
Proof.
  intros. simpl. rewrite 顶迭代后继次, (幂运算_改写_右 (ε α * ω)), 指数积运算律.
  apply 幂运算_改写_左, ε数为不动点. auto. apply ε'顶ω塔1层.
Qed.

Fact ε'顶ω塔3层 : ∀ α, (ω ^^ᵀ [3]) (ε α)⁺ ≃ ε α ^ (ε α ^ ω).
Proof with auto.
  intros. simpl. rewrite 顶迭代后继次, (幂运算_改写_右 (ε α ^ ω))... 2: apply ε'顶ω塔2层.
  rewrite (幂运算_改写_右 (ε α * ε α ^ ω))...
  rewrite 指数积运算律. apply 幂运算_改写_左. apply ε数为不动点.
  rewrite (幂运算_改写_右 ([1] + ω)) at 1...
  rewrite 指数和运算律. apply 乘法_改写_左. rewrite 一次幂. reflexivity.
  rewrite 一加ω弱等于ω. reflexivity.
Qed.

Lemma ε'顶ω塔n'层等于ω顶ε塔n层 : ∀ α n, 良构 α → (ω ^^ᵀ [S (S n)]) (ε α)⁺ ≃ (ε α ^^ᵀ [S n]) ω.
Proof with auto.
  intros * WF. induction n.
  - rewrite ε'顶ω塔2层, 顶迭代一次. reflexivity.
  - simpl. do 4 rewrite 顶迭代后继次.
    simpl in IHn. do 2 rewrite 顶迭代后继次 in IHn.
    rewrite (@幂运算_改写_右 (ε α))... 2: symmetry; apply IHn... clear IHn.
    rewrite (@幂运算_改写_左 (ε α)). 2: symmetry; apply ε数为不动点.
    rewrite <- 指数积运算律. apply 幂运算_改写_右...
    rewrite (@乘法_改写_左 (ε α)). 2: symmetry; apply ε数为不动点.
    rewrite <- 指数和运算律. apply 幂运算_改写_右...
    rewrite (@加法_改写_左 (ε α)). 2: symmetry; apply ε数为不动点. 
    rewrite ω幂对加法的吸收律. reflexivity.
    + induction n. simpl. apply ε保良构...
      simpl. rewrite 顶迭代后继次. apply 幂运算保良构...
    + induction n. rewrite 顶迭代零次... simpl. rewrite 顶迭代后继次...
      apply 强弱传递 with ((ω ^^ᵀ [n]) (ε α)⁺)... apply 幂运算_弱放大_左...
Qed.

Lemma ε'顶ω塔极限等于ω顶ε塔极限 : ∀ α, 良构 α → (ω ^^ᵀ ω) (ε α)⁺ ≃ (ε α ^^ᵀ ω) ω.
Proof with auto.
  intros. unfold ω at 2 3. rewrite 顶迭代极限次, 顶迭代极限次.
  rewrite 序列极限与起始无关, 序列极限与起始无关.
  2: { rewrite 顶迭代一次. simpl. rewrite 顶迭代后继次, 顶迭代一次.
    apply 幂运算_弱保序_右... apply 幂运算_弱放大_左... }
  2: { rewrite 顶迭代零次, 顶迭代一次. apply 幂运算_弱放大_左... }
  rewrite (序列极限与起始无关 (λ n, (ε α ^^ᵀ [n]) ω)).
  2: { rewrite 顶迭代零次, 顶迭代一次. apply 幂运算_弱放大_左... }
  split; constructor; intros n.
  - rewrite ε'顶ω塔n'层等于ω顶ε塔n层... apply 弱序_极限_介入 with n. reflexivity.
  - rewrite <- ε'顶ω塔n'层等于ω顶ε塔n层... apply 弱序_极限_介入 with n. reflexivity.
Qed.

Theorem ε_后继_ε塔 : ∀ α, 良构 α → ε α⁺ ≃ (ε α ^^ᴸ ω).
Proof with auto.
  intros. rewrite ε_后继_ω塔, ε'顶ω塔极限等于ω顶ε塔极限, 无穷顶迭代等于左迭代... reflexivity.
  apply 小于即后继小于等于. rewrite <- ε数为不动点... apply 小于即后继小于等于. apply 幂运算_强放大_右...
Qed.

Definition ζ := ε′.

Fact ζ为序数嵌入 : 序数嵌入 ζ.
Proof. apply 不动点枚举为序数嵌入. apply ε为序数嵌入. Qed.

Fact ζ_零 : ζ [0] = Itω ε [0].
Proof. easy. Qed.

Fact ζ_后继 : ∀ α, ζ α⁺ = Itω ε (ζ α)⁺.
Proof. easy. Qed.

Fact ζ_极限 : ∀ f, ζ (lim f) ≃ lim (λ n, ζ (f n)).
Proof. easy. Qed.

Fact ζ保良构 : 保良构 ζ.
Proof with auto.
  intros. apply 不动点枚举保良构_递进...
  - apply 幂运算为序数嵌入...
  - rewrite 零次幂. simpl...
  - apply 以ω为底的幂运算在后继处强放大.
  - apply ε保良构.
Qed.

Definition η := ζ′.

Fact η为序数嵌入 : 序数嵌入 η.
Proof. apply 不动点枚举为序数嵌入. apply ζ为序数嵌入. Qed.

Fact η_零 : η [0] = Itω ζ [0].
Proof. easy. Qed.

Fact η_后继 : ∀ α, η α⁺ = Itω ζ (η α)⁺.
Proof. easy. Qed.

Fact η_极限 : ∀ f, η (lim f) ≃ lim (λ n, η (f n)).
Proof. easy. Qed.

Fact η保良构 : 保良构 η.
Proof with auto.
  intros. apply 不动点枚举保良构_递进...
  - apply ε为序数嵌入.
  - apply ε在零处强放大.
  - apply ε在良构后继处强放大.
  - apply ζ保良构.
Qed.
