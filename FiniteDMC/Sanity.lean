/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import FiniteDMC.Channel
import Mathlib.Probability.Distributions.Uniform

/-!
# Sanity checks on the definitional layer

None of the top-level theorems depend on this file.  It exists so that the definitions in
`FiniteDMC.Entropy` and `FiniteDMC.Channel` cannot be silently degenerate: each check below is a
closed statement with a real proof and no `sorry`.

These are deliberately checks of *conventions*, since those are what a reader has to take on trust
when reviewing the top-level statements:

* entropy is measured in **bits** (a fair coin carries exactly `1`);
* the `0 * log 0 = 0` convention holds (a point mass carries exactly `0`), so `entropy` needs no
  support hypothesis;
* the `n`-fold extension of a channel really is **memoryless** (its transition law is the product),
  and its length-`1` case is faithful to the original channel.
-/

namespace FiniteDMC

open Finset

/-- Entropy is measured in bits: a fair coin has entropy exactly `1`. -/
example : entropy (PMF.uniformOfFintype Bool) = 1 := by
  simp [entropy, PMF.uniformOfFintype_apply, Real.logb]
  field_simp

/-- The `0 * log 0 = 0` convention: a point mass has entropy exactly `0`, with no hypothesis about
the support. -/
example {α : Type*} [Fintype α] [DecidableEq α] (a : α) : entropy (PMF.pure a) = 0 := by
  simp [entropy, PMF.pure_apply, apply_ite ENNReal.toReal]

/-- Memorylessness is definitional: the `n`-fold extension's transition law is the product of the
per-symbol transition laws, by `rfl`. -/
example {X Y : Type*} [Fintype X] [Fintype Y] (W : DMC X Y) (n : ℕ) (x : Fin n → X)
    (y : Fin n → Y) : (W.power n).transition x y = ∏ i, W.transition (x i) (y i) := rfl

/-- The length-`1` extension is faithful to the original channel. -/
example {X Y : Type*} [Fintype X] [Fintype Y] (W : DMC X Y) (x : Fin 1 → X) (y : Fin 1 → Y) :
    (W.power 1).transition x y = W.transition (x 0) (y 0) := by
  simp

end FiniteDMC
