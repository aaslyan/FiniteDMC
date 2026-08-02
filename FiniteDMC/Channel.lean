/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import FiniteDMC.Entropy

/-!
# Finite discrete memoryless channels and their capacity

A finite discrete memoryless channel (DMC) with finite input alphabet `X` and finite output
alphabet `Y` is a stochastic matrix, i.e. a map `X → PMF Y`.

## Main definitions

* `FiniteDMC.DMC X Y` : a finite DMC.
* `FiniteDMC.DMC.power W n` : the `n`-fold memoryless extension `Wⁿ`, a DMC from `Fin n → X` to
  `Fin n → Y`.  Memorylessness is *manifest*: the transition law is literally the product
  `∏ i, W (y i ∣ x i)`, not a property proved after the fact.
* `FiniteDMC.DMC.joint W p` : the joint input-output law on `X × Y` induced by an input law `p`.
* `FiniteDMC.DMC.mutualInfo W p` : `I(p ; W)`, the mutual information across `W` at input law `p`.
* `FiniteDMC.DMC.capacity W` : `C = sup_p I(p ; W)`, in bits per channel use.

## Implementation notes

* **Blocks are `Fin n → X`, not `Vector X n`.**  `Fin n → X` is automatically a `Fintype`, the
  product `∏ i, W (y i ∣ x i)` is a plain `Finset.prod`, and `Mathlib`'s `List.Vector` API is
  explicitly documented as incomplete.  See `GOAL.md` (decision D-3).
* **Capacity is a supremum, not a maximum.**  `sSup` over the range of `p ↦ I(p ; W)`.  That the
  supremum is attained is a separate later theorem requiring compactness of the simplex and
  continuity of `mutualInfo`; it is deliberately *not* a prerequisite for stating capacity.
  See `GOAL.md` (decision D-7).
-/

namespace FiniteDMC

open Finset

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A discrete memoryless channel with finite input alphabet `X` and finite output alphabet `Y`:
a stochastic matrix, presented as a map from inputs to output distributions. -/
structure DMC (X Y : Type*) [Fintype X] [Fintype Y] where
  /-- `transition x` is the output distribution given input `x`. -/
  transition : X → PMF Y

/-- The transition probabilities of the `n`-fold memoryless extension of `W` sum to `1`.

This is the normalisation obligation for `DMC.power`; it is `Fintype.prod_sum` together with the
fact that each row of `W` sums to `1`. -/
theorem power_sum_eq_one (W : DMC X Y) (n : ℕ) (x : Fin n → X) :
    ∑ y : Fin n → Y, ∏ i, W.transition (x i) (y i) = 1 := by
  sorry

/-- The `n`-fold memoryless extension `Wⁿ` of a DMC `W`: a DMC from length-`n` input blocks to
length-`n` output blocks whose transition law is the product of the per-symbol transition laws.

Memorylessness is built into the definition rather than being an extra hypothesis. -/
noncomputable def DMC.power (W : DMC X Y) (n : ℕ) : DMC (Fin n → X) (Fin n → Y) where
  transition x := PMF.ofFintype (fun y ↦ ∏ i, W.transition (x i) (y i)) (power_sum_eq_one W n x)

@[simp]
theorem DMC.power_transition_apply (W : DMC X Y) (n : ℕ) (x : Fin n → X) (y : Fin n → Y) :
    (W.power n).transition x y = ∏ i, W.transition (x i) (y i) := rfl

/-- The joint input-output distribution on `X × Y` obtained by feeding the input law `p` into the
channel `W`. -/
noncomputable def DMC.joint (W : DMC X Y) (p : PMF X) : PMF (X × Y) :=
  p.bind fun x ↦ (W.transition x).map fun y ↦ (x, y)

/-- The mutual information `I(p ; W)` between the input and the output of `W` when the input is
distributed according to `p`, in bits. -/
noncomputable def DMC.mutualInfo (W : DMC X Y) (p : PMF X) : ℝ :=
  FiniteDMC.mutualInfo (W.joint p)

/-- The capacity `C = sup_p I(p ; W)` of a finite DMC, in bits per channel use.

Stated as a supremum: attainment is a separate theorem, not a prerequisite. -/
noncomputable def DMC.capacity (W : DMC X Y) : ℝ :=
  sSup (Set.range fun p : PMF X ↦ W.mutualInfo p)

/-- The set of achievable mutual informations of a finite DMC is bounded above.

Needed for `sSup` to mean what it should: without it `DMC.capacity` would be the junk value `0`.
Mathematically `I(p ; W) ≤ log₂ (Fintype.card X)`, but any bound will do. -/
theorem bddAbove_range_mutualInfo (W : DMC X Y) :
    BddAbove (Set.range fun p : PMF X ↦ W.mutualInfo p) := by
  sorry

end FiniteDMC
