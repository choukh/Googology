(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.Arithmetic.
Require Import GOO.Ordinal.Iteration.
Require Import GOO.Ordinal.EpsilonNumbers.

Local Open Scope 序数符号域.

Fixpoint φ α :=
  match α with
  | ∅ => λ ξ, ω ^ ξ
  | α⁺ => (φ α)′
  | lim f => λ α, lim (λ n, φ (f n) α)
  end.

Definition ε := φ [1].
Definition ζ := φ [2].
Definition η := φ [3].
Definition Γ := Itω (λ ξ, φ ξ ∅).
