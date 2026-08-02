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

This file holds the definitions themselves together with the small `PMF` utilities they need on a
`Fintype`.  Genuine *bounds* on entropy live in `FiniteDMC.EntropyBounds`; the split keeps this
file reviewable as the definitional layer, where a wrong choice is expensive.

## Main definitions

* `FiniteDMC.entropy p` : the Shannon entropy `H(p)`, in bits, of `p : PMF α` with `α` a `Fintype`.
* `FiniteDMC.condEntropy μ` : the conditional entropy `H(A ∣ B)` of a joint law `μ : PMF (α × β)`.
* `FiniteDMC.mutualInfo μ` : the mutual information `I(A ; B)` of a joint law `μ : PMF (α × β)`.

Supporting `PMF` facts on a `Fintype`: `sum_coe_eq_one`, `sum_toReal_eq_one`, `nonempty_of_pmf`,
`map_apply_fintype`, `sum_map_toReal_mul`, `map_snd_apply`, `le_map_snd`.

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

variable {α β Z : Type*}

set_option linter.unusedFintypeInType false in
/-- The masses of a `PMF` on a finite type sum to `1`. -/
theorem sum_coe_eq_one [Fintype α] (p : PMF α) : ∑ a, p a = 1 := by
  rw [← p.tsum_coe, tsum_fintype]

/-- The real-valued masses of a `PMF` on a finite type sum to `1`. -/
theorem sum_toReal_eq_one [Fintype α] (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum fun a _ ↦ p.apply_ne_top a, sum_coe_eq_one, ENNReal.toReal_one]

/-- A type carrying a `PMF` is nonempty. -/
theorem nonempty_of_pmf (p : PMF α) : Nonempty α := by
  by_contra hα
  rw [not_nonempty_iff] at hα
  have h := p.tsum_coe
  simp at h

/-- `PMF.map` evaluated on a finite type, as a `Finset` sum. -/
theorem map_apply_fintype [Fintype α] [DecidableEq β] (f : α → β) (p : PMF α) (b : β) :
    (p.map f) b = ∑ a, if b = f a then p a else 0 := by
  rw [PMF.map_apply, tsum_fintype]
  exact Finset.sum_congr rfl fun a _ ↦ by convert rfl

/-- Change of variables against a pushforward law: summing a weight `g` against `p.map f` is the
same as summing `g ∘ f` against `p`. -/
theorem sum_map_toReal_mul [Fintype α] [Fintype β] (p : PMF α) (f : α → β)
    (g : β → ℝ) : ∑ b, ((p.map f) b).toReal * g b = ∑ a, (p a).toReal * g (f a) := by
  classical
  have h : ∀ b : β, ((p.map f) b).toReal = ∑ a, (if b = f a then p a else 0).toReal := by
    intro b
    rw [map_apply_fintype, ENNReal.toReal_sum]
    intro a _
    split
    · exact p.apply_ne_top a
    · simp
  simp_rw [h, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_eq_single (f a)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

-- In this lemma and the two below, the `Fintype` instances are used by the proofs, via
-- `map_apply_fintype`, even though they do not appear in the statements.
set_option linter.unusedFintypeInType false in
/-- The second marginal, evaluated as a sum. -/
theorem map_snd_apply [Fintype α] [Fintype β] (μ : PMF (α × β)) (b : β) :
    (μ.map Prod.snd) b = ∑ a, μ (a, b) := by
  classical
  rw [map_apply_fintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc; simp [Ne.symm hc]
  · simp

set_option linter.unusedFintypeInType false in
/-- A mass is dominated by the mass its pushforward puts on the image point. -/
theorem le_map_apply {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (f : α → β) (a : α) :
    p a ≤ (p.map f) (f a) := by
  classical
  rw [map_apply_fintype]
  calc p a = if f a = f a then p a else 0 := by simp
    _ ≤ ∑ a', if f a = f a' then p a' else 0 :=
        Finset.single_le_sum (f := fun a' ↦ if f a = f a' then p a' else 0)
          (fun i _ ↦ _root_.zero_le) (Finset.mem_univ a)

set_option linter.unusedFintypeInType false in
/-- A joint mass is dominated by its second marginal. -/
theorem le_map_snd [Fintype α] [Fintype β] (μ : PMF (α × β)) (a : α) (b : β) :
    μ (a, b) ≤ (μ.map Prod.snd) b := le_map_apply μ Prod.snd (a, b)

/-- Summing a product weight against a function of a single coordinate collapses to that
coordinate's factor. -/
theorem sum_prod_mul {R : Type*} [CommSemiring R] [Fintype β] {n : ℕ} (t : Fin n → β → R)
    (ht : ∀ j, ∑ a, t j a = 1) (i : Fin n) (g : β → R) :
    ∑ y : Fin n → β, (∏ j, t j (y j)) * g (y i) = ∑ a, t i a * g a := by
  classical
  have hpt : ∀ y : Fin n → β, (∏ j, t j (y j)) * g (y i)
      = ∏ j, (if j = i then t j (y j) * g (y j) else t j (y j)) := by
    intro y
    rw [← Finset.mul_prod_erase Finset.univ
          (fun j ↦ if j = i then t j (y j) * g (y j) else t j (y j)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (fun j ↦ t j (y j)) (Finset.mem_univ i), if_pos rfl,
      Finset.prod_congr rfl (fun j hj ↦ if_neg (Finset.ne_of_mem_erase hj))]
    ring
  rw [Finset.sum_congr rfl fun y _ ↦ hpt y,
    ← Fintype.prod_sum (fun (j : Fin n) (a : β) ↦ if j = i then t j a * g a else t j a),
    ← Finset.mul_prod_erase Finset.univ
        (fun j ↦ ∑ a, if j = i then t j a * g a else t j a) (Finset.mem_univ i)]
  rw [Finset.prod_congr rfl (fun j hj ↦ by
      simp only [if_neg (Finset.ne_of_mem_erase hj)]; exact ht j),
    Finset.prod_const_one, mul_one]
  simp

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
