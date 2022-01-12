# Constructive ordinals and formalized googology

## Feature
- Constructive approach based on CIC
- Does not require axioms or LEM
- Up to Small Veblen Ordinal
- Ready for googology function such as fast growing hierarchy

## Contents

- Ordinal/
  - Ord.v
    - Inductive definition of Brouwer ordinal
    - Inductive definition of weak ordering "≤"
    - Equality "≃" and strong ordering "<" are defined by "≤"
    - Partial order of "≤" and strict order of "<" are proved
    - No total order, but that's fine
  - WellFormed.v
    - Well formed (WF) ordinals are those constructed by strictly increasing sequence all the way up
    - Function f is WF preserving iff forall WF α, f(α) is WF
  - Operation.v
    - Common properties of ordinal functions are defined
    - Definition of normal function is adapted for the absence of total order
  - Recursion.v
    - Continuous (on limit ordianl) recursive function is defined and its properties are proved
  - Arithmetic.v
    - Addition, multiplication, exponentiation are defined by recursion and their WF preserving properties are proved
    - Association law, distribution law, etc
  - Tetration.v
    - We proved that α ^^ ω⁺ ≃ α ^^ ω
    - And α ^^ β ≃ α ^^ ω forall β ≥ ω
  - Iteration.v
    - Infinite iteration (Itω) of function is defined
    - Itω is equivalent to recursion up to ω
    - If f is normal then Itω(f, α) is a veblen fixed point not less than α
    - Recursion of Itω(f, α⁺) is f's veblen fixed point yielding function, shorten as f'
    - We proved that f' is normal if f is normal
    - And f' is WF preserving if f is WF preserving
  - EpsilonNumbers.v
    - ε function is defined as (λ ξ, ω ^ ξ)'
    - We proved that ε(α⁺) ≃ ω ^ ω ^ ... ^ ε(α)⁺ for all α but only for WF α, ε(α⁺) ≃ ε(α) ^^ ω can be proved
    - ζ is defined as ε' and η as ζ'
    - ε, ζ, η, ... are all normal and WF preserving
  - VeblenFunction.v
    - Veblen function φ(α, β) is defined
    - Γ is defined as Itω(λ ξ, φ(ξ, 0))
  - ExtendedVeblenFunction.v (TODO)
    - SVO and LVO
- Function/
  - FGH.v
    - Fast growing hierachy that suitable for ordinals we defined

## Requirement
```
Coq 8.14.1
```

## Compile
```
make
```
