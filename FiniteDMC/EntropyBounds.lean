/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import FiniteDMC.Entropy
import Mathlib.Probability.Distributions.Uniform

/-!
# Basic bounds on Shannon entropy

The first layer of actual entropy theory, as opposed to the definitions in `FiniteDMC.Entropy`.
Mathlib has none of this for distributions on a `Fintype`, so it is built here.

Everything rests on one analytic fact, `Real.log_le_sub_one_of_pos`; there is no appeal to Jensen's
inequality or to convexity machinery.

## Main statements

* `FiniteDMC.entropy_nonneg` : `0 ≤ H(p)`.
* `FiniteDMC.entropy_le_crossEntropy` : Gibbs' inequality, `H(p) ≤ -∑ p log₂ q`.
* `FiniteDMC.entropy_le_logb_card` : the maximum-entropy bound `H(p) ≤ log₂ |α|`.

## Implementation notes

Gibbs' inequality is stated with the absolute-continuity hypothesis `∀ a, q a = 0 → p a = 0`
rather than `∀ a, 0 < q a`. The weaker form is what Fano's inequality needs, because there the
reference law is built from an output marginal that may genuinely vanish somewhere.
-/

namespace FiniteDMC

open Finset

variable {α : Type*}

/-- The real-valued mass of a `PMF` lies in `[0, 1]`. -/
theorem toReal_apply_le_one (p : PMF α) (a : α) : (p a).toReal ≤ 1 := by
  rw [← ENNReal.toReal_one]
  exact (ENNReal.toReal_le_toReal (p.apply_ne_top a) ENNReal.one_ne_top).2 (p.coe_le_one a)

variable [Fintype α]

/-- Shannon entropy is nonnegative. -/
theorem entropy_nonneg (p : PMF α) : 0 ≤ entropy p := by
  rw [entropy, neg_nonneg]
  refine Finset.sum_nonpos fun a _ ↦ ?_
  have h0 : (0 : ℝ) ≤ (p a).toReal := ENNReal.toReal_nonneg
  have hlog := Real.logb_nonpos one_lt_two h0 (toReal_apply_le_one p a)
  nlinarith

/-- **Gibbs' inequality**: the entropy of `p` is at most its cross-entropy against any reference
law `q` that does not vanish where `p` does not. -/
theorem entropy_le_crossEntropy (p q : PMF α) (h : ∀ a, q a = 0 → p a = 0) :
    entropy p ≤ -∑ a, (p a).toReal * Real.logb 2 (q a).toReal := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  -- The whole content, in natural logarithms.
  have key : ∑ a, (p a).toReal * (Real.log (q a).toReal - Real.log (p a).toReal) ≤ 0 := by
    have step : ∀ a ∈ Finset.univ,
        (p a).toReal * (Real.log (q a).toReal - Real.log (p a).toReal)
          ≤ (q a).toReal - (p a).toReal := by
      intro a _
      rcases eq_or_lt_of_le (ENNReal.toReal_nonneg : (0 : ℝ) ≤ (p a).toReal) with hp | hp
      · rw [← hp]
        simp
      · have hq0 : q a ≠ 0 := by
          intro hq
          rw [h a hq] at hp
          simp at hp
        have hq : (0 : ℝ) < (q a).toReal := ENNReal.toReal_pos hq0 (q.apply_ne_top a)
        have hdiv := Real.log_le_sub_one_of_pos (div_pos hq hp)
        rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp)] at hdiv
        have hmul := mul_le_mul_of_nonneg_left hdiv hp.le
        have heq : (p a).toReal * ((q a).toReal / (p a).toReal - 1)
            = (q a).toReal - (p a).toReal := by
          field_simp
        linarith
    calc ∑ a, (p a).toReal * (Real.log (q a).toReal - Real.log (p a).toReal)
        ≤ ∑ a, ((q a).toReal - (p a).toReal) := Finset.sum_le_sum step
      _ = 0 := by
          rw [Finset.sum_sub_distrib, sum_toReal_eq_one, sum_toReal_eq_one, sub_self]
  -- Convert to base 2 and rearrange.
  rw [entropy, neg_le_neg_iff, ← sub_nonpos, ← Finset.sum_sub_distrib]
  have hrw : ∀ a : α, (p a).toReal * Real.logb 2 (q a).toReal
      - (p a).toReal * Real.logb 2 (p a).toReal
      = (p a).toReal * (Real.log (q a).toReal - Real.log (p a).toReal) / Real.log 2 := by
    intro a
    simp only [Real.logb]
    ring
  rw [Finset.sum_congr rfl fun a _ ↦ hrw a, ← Finset.sum_div]
  exact div_nonpos_of_nonpos_of_nonneg key hlog2.le

/-- **Maximum entropy**: a distribution on a finite type has entropy at most `log₂` of the
cardinality, attained by the uniform law. -/
theorem entropy_le_logb_card [Nonempty α] (p : PMF α) :
    entropy p ≤ Real.logb 2 (Fintype.card α) := by
  have hcard : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast Fintype.card_pos
  have hne : ∀ a : α, (PMF.uniformOfFintype α) a = 0 → p a = 0 := by
    intro a ha
    rw [PMF.uniformOfFintype_apply] at ha
    rw [ENNReal.inv_eq_zero] at ha
    exact absurd ha (by simp)
  refine (entropy_le_crossEntropy p (PMF.uniformOfFintype α) hne).trans_eq ?_
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Real.logb_inv, mul_neg, Finset.sum_neg_distrib, neg_neg, ← Finset.sum_mul,
    sum_toReal_eq_one, one_mul]

end FiniteDMC
