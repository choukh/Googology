(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.Recursion.
Require Import GOO.Ordinal.Iteration.

Local Open Scope 序数域.

Fixpoint 序元 ι :=
  match ι with
  | ∅ => 序数
  | ι⁺ => 序数 → 序元 ι
  | lim f => ∀ n, 序元 (f n)
  end.

Reserved Notation "f '∅..'" (at level 20).
Fixpoint 充零 {ι} (f : 序元 ι) : 序数 :=
  match ι, f with
  | ∅, f => f
  | _⁺, f => f ∅ ∅..
  | lim _, f => f 0 ∅..
  end
where "f ∅.." := (充零 f) : 序数域.

Reserved Notation "f '∅.._'" (at level 20).
Fixpoint 充零留一 {ι} (f : 序元 ι⁺) : 序元 [1] :=
  match ι, f with
  | ∅, f => f
  | _⁺, f => f ∅ ∅.._
  | lim _, f => (λ _, f ∅ 1) ∅.._
  end
where "f ∅.._" := (充零留一 f) : 序数域.

Reserved Notation "f '∅..__'" (at level 20).
Fixpoint 充零留二 {ι} (f : 序元 ι⁺⁺) : 序元 [2] :=
  match ι, f with
  | ∅, f => f
  | _⁺, f => f ∅ ∅..__
  | lim _, f => (λ _ _, f ∅ ∅ 2) ∅..__
  end
where "f ∅..__" := (充零留二 f) : 序数域.


