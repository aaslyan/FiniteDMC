/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Shannon entropy and mutual information for distributions on finite types

This file introduces the *minimum* information-theoretic vocabulary needed to even **state** the
capacity of a finite discrete memoryless channel and the weak converse.  Mathlib currently has
`Real.negMulLog`, the binary entropy function, and a measure-theoretic Kullback-Leibler divergence,
but no Shannon entropy or mutual information for distributions on a `Fintype`, so we define them
here.

Nothing beyond the definitions and one identity that holds by `ring` is developed: every genuine
property of entropy is deferred to a named `sorry` at the point where a proof actually demands it.

## Main definitions

* `FiniteDMC.entropy p` : the Shannon entropy `H(p)`, in bits, of `p : PMF α` with `α` a `Fintype`.
* `FiniteDMC.condEntropy μ` : the conditional entropy `H(A ∣ B)` of a joint law `μ : PMF (α × β)`.
* `FiniteDMC.mutualInfo μ` : the mutual information `I(A ; B)` of a joint law `μ : PMF (α × β)`.

## Implementation notes

* **Base 2.** All logarithms are `Real.logb 2`, so entropy is measured in bits.
* **Real-valued.** `PMF` takes values in `ℝ≥0∞`; we push through `ENNReal.toReal` at the point of
  use.  This is total and lossless here because a `PMF` never takes the value `∞`.
* **`0 * log 0 = 0` is automatic.** `Real.logb 2 0 = 0` by Lean's junk-value convention for `log`,
  and `0 * x = 0`, so `entropy` needs no side condition and no case split.  The convention is the
  mathematically standard one, but note that it is being obtained from a junk value rather than
  stated; see `GOAL.md` (decision D-4).
* **`mutualInfo` is defined by inclusion-exclusion**, `I = H(A) + H(B) - H(A,B)`, rather than as a
  relative entropy `∑ p log (p / (p ⊗ p))`.  The former is total: it involves no division and so no
  hypothesis about the conditioning event having positive mass.  See `GOAL.md` (decision D-5).
-/

namespace FiniteDMC

open Finset

variable {α β : Type*}

/-- The Shannon entropy `H(p) = -∑ a, p a * log₂ (p a)` of a distribution on a finite type,
measured in bits. -/
noncomputable def entropy [Fintype α] (p : PMF α) : ℝ :=
  -∑ a : α, (p a).toReal * Real.logb 2 (p a).toReal

/-- The conditional entropy `H(A ∣ B) = H(A, B) - H(B)` of a joint distribution `μ` on `α × β`,
measured in bits. -/
noncomputable def condEntropy [Fintype α] [Fintype β] (μ : PMF (α × β)) : ℝ :=
  entropy μ - entropy (μ.map Prod.snd)

/-- The mutual information `I(A ; B) = H(A) + H(B) - H(A, B)` of a joint distribution `μ` on
`α × β`, measured in bits. -/
noncomputable def mutualInfo [Fintype α] [Fintype β] (μ : PMF (α × β)) : ℝ :=
  entropy (μ.map Prod.fst) + entropy (μ.map Prod.snd) - entropy μ

/-- The chain rule `H(A) = I(A ; B) + H(A ∣ B)`.

With `mutualInfo` and `condEntropy` defined by inclusion-exclusion this is an algebraic identity,
so it costs nothing.  It is the backbone of the weak converse, where it turns the entropy of the
uniform message into an information term plus a Fano term. -/
theorem entropy_map_fst_eq_mutualInfo_add_condEntropy [Fintype α] [Fintype β] (μ : PMF (α × β)) :
    entropy (μ.map Prod.fst) = mutualInfo μ + condEntropy μ := by
  simp only [mutualInfo, condEntropy]
  ring

end FiniteDMC
