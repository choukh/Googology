(* Copyright (c) 2022, choukh <choukyuhei@gmail.com> *)

Require Import GOO.Ordinal.Ord.
Require Import GOO.Ordinal.Iteration.
Require Import GOO.Ordinal.VeblenFunction.
Require Import GOO.Ordinal.ExtendedVeblenFunction.

Local Open Scope 序数域.

Definition φ_1atω_1at0 := lim (λ n, φ (S n) SVO⁺ ∅..).

(* TODO *)
