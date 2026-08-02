/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import FiniteDMC.Code
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The weak converse to the channel coding theorem

If a sequence of block codes for a finite DMC `W` has rate at least `R` and average error
probability tending to `0`, then `R ≤ C`.

The top-level argument here is complete: `weak_converse` is proved outright from six named facts,
each a standard piece of information theory stated at exactly the type the argument needs, and
each left as a `sorry` for now.

## Main statements

* `FiniteDMC.logb_card_le_capacity` : the one-shot Fano bound
  `log₂ |M| ≤ n * C + 1 + Pe * log₂ |M|`.
* `FiniteDMC.BlockCode.rate_mul_one_sub_avgError_le` : the same bound in rate form,
  `rate * (1 - Pe) ≤ C + 1 / n`, which is what both asymptotic statements consume.
* `FiniteDMC.weak_converse` : the weak converse in `R`-form.
* `FiniteDMC.weak_converse_limsup` : the weak converse in `limsup`-form.

## Implementation notes

The `R`-form is primary and the `limsup`-form is derived, because `Filter.limsup` on `ℝ` is
`sInf` of the set of eventual upper bounds and so evaluates to the junk value `0` when the rates
are unbounded above.  Without a boundedness hypothesis the `limsup` statement would be *weaker*
than it looks: it would be satisfied vacuously by a code sequence with unbounded rate.  See
`GOAL.md` (decision D-10).
-/

namespace FiniteDMC

open Filter Topology

variable {X Y : Type*} [Fintype X] [Fintype Y] {n : ℕ}

/-! ### Facts consumed by the converse -/

/-- The average error probability is at most `1`. -/
theorem BlockCode.avgError_le_one (c : BlockCode X Y n) (W : DMC X Y) : c.avgError W ≤ 1 := by
  sorry

/-- The entropy of the uniform message law is `log₂ |M|`. -/
theorem BlockCode.entropy_messageDist (c : BlockCode X Y n) :
    entropy c.messageDist = Real.logb 2 c.card := by
  sorry

/-- The message marginal of the joint message-output law is the uniform message law. -/
theorem BlockCode.msgOutJoint_map_fst (c : BlockCode X Y n) (W : DMC X Y) :
    (c.msgOutJoint W).map Prod.fst = c.messageDist := by
  sorry

/-- **Fano's inequality**, specialised to a block code: the residual uncertainty about the message
given the channel output is controlled by the average error probability.

The `1` on the right is the usual crude bound `h₂(Pe) ≤ 1` for the binary entropy of `Pe`. -/
theorem BlockCode.fano_inequality (c : BlockCode X Y n) (W : DMC X Y) :
    condEntropy (c.msgOutJoint W) ≤ 1 + c.avgError W * Real.logb 2 c.card := by
  sorry

/-- **Data processing inequality** for the Markov chain `M → Xⁿ → Yⁿ` induced by a block code:
the encoder cannot increase the information the output carries about the message. -/
theorem BlockCode.mutualInfo_msgOutJoint_le (c : BlockCode X Y n) (W : DMC X Y) :
    mutualInfo (c.msgOutJoint W) ≤ mutualInfo (c.inOutJoint W) := by
  sorry

/-- **Single-letterisation**: `n` uses of a memoryless channel carry at most `n * C` bits,
whatever the joint law of the input block. -/
theorem DMC.mutualInfo_power_le (W : DMC X Y) (n : ℕ) (q : PMF (Fin n → X)) :
    (W.power n).mutualInfo q ≤ n * W.capacity := by
  sorry

/-! ### The converse -/

/-- The one-shot Fano bound for a block code: `log₂ |M| ≤ n * C + 1 + Pe * log₂ |M|`.

This is the whole converse chain
`log₂ |M| = H(M) = I(M ; Yⁿ) + H(M ∣ Yⁿ) ≤ I(Xⁿ ; Yⁿ) + H(M ∣ Yⁿ) ≤ n * C + 1 + Pe * log₂ |M|`,
assembled from the facts above. -/
theorem logb_card_le_capacity (c : BlockCode X Y n) (W : DMC X Y) :
    Real.logb 2 c.card ≤ n * W.capacity + 1 + c.avgError W * Real.logb 2 c.card := by
  have hchain := entropy_map_fst_eq_mutualInfo_add_condEntropy (c.msgOutJoint W)
  rw [c.msgOutJoint_map_fst W, c.entropy_messageDist] at hchain
  have hfano := c.fano_inequality W
  have hdpi := c.mutualInfo_msgOutJoint_le W
  have hsingle : mutualInfo (c.inOutJoint W) ≤ n * W.capacity :=
    W.mutualInfo_power_le n (c.messageDist.map c.encode)
  linarith

/-- The one-shot Fano bound, restated in terms of the rate: for every positive block length,
`rate * (1 - Pe) ≤ C + 1 / n`.

This is the single per-block-length inequality that both asymptotic forms of the converse
consume. -/
theorem BlockCode.rate_mul_one_sub_avgError_le (c : BlockCode X Y n) (W : DMC X Y) (hn : 0 < n) :
    c.rate * (1 - c.avgError W) ≤ W.capacity + 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : Real.logb 2 c.card = n * c.rate := by
    rw [BlockCode.rate]; field_simp
  have h1 := logb_card_le_capacity c W
  rw [hcard] at h1
  have hmul : (n : ℝ) * (c.rate * (1 - c.avgError W)) ≤ (n : ℝ) * (W.capacity + 1 / n) := by
    have hrw : (n : ℝ) * (W.capacity + 1 / n) = n * W.capacity + 1 := by field_simp
    rw [hrw]
    nlinarith [h1]
  exact le_of_mul_le_mul_left hmul hn'

/-- **Weak converse to the channel coding theorem.**  A sequence of block codes for a finite DMC
whose rates are all at least `R` and whose average error probabilities tend to `0` forces
`R ≤ C`. -/
theorem weak_converse (W : DMC X Y) {R : ℝ} (codes : ∀ n, BlockCode X Y n)
    (hrate : ∀ n, R ≤ (codes n).rate)
    (herr : Tendsto (fun n ↦ (codes n).avgError W) atTop (𝓝 0)) :
    R ≤ W.capacity := by
  have key : ∀ᶠ n : ℕ in atTop, R * (1 - (codes n).avgError W) ≤ W.capacity + 1 / n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hbase := (codes n).rate_mul_one_sub_avgError_le W hn
    have hone := (codes n).avgError_le_one W
    nlinarith [mul_nonneg (sub_nonneg.mpr (hrate n)) (sub_nonneg.mpr hone)]
  have hf : Tendsto (fun n : ℕ ↦ R * (1 - (codes n).avgError W)) atTop (𝓝 R) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hR : Tendsto (fun _ : ℕ ↦ R) atTop (𝓝 R) := tendsto_const_nhds
    simpa using hR.mul (hone.sub herr)
  have hg : Tendsto (fun n : ℕ ↦ W.capacity + 1 / (n : ℝ)) atTop (𝓝 W.capacity) := by
    have hC : Tendsto (fun _ : ℕ ↦ W.capacity) atTop (𝓝 W.capacity) := tendsto_const_nhds
    simpa using hC.add tendsto_one_div_atTop_nhds_zero_nat
  exact le_of_tendsto_of_tendsto hf hg key

/-- The weak converse in `limsup` form.

The boundedness hypothesis is essential and not cosmetic: `Filter.limsup` on `ℝ` is defined as an
`sInf`, so for a rate sequence that is unbounded above it takes the junk value `0` and the
conclusion would hold vacuously. -/
theorem weak_converse_limsup (W : DMC X Y) (codes : ∀ n, BlockCode X Y n)
    (hbdd : BddAbove (Set.range fun n ↦ (codes n).rate))
    (herr : Tendsto (fun n ↦ (codes n).avgError W) atTop (𝓝 0)) :
    limsup (fun n ↦ (codes n).rate) atTop ≤ W.capacity := by
  sorry

end FiniteDMC
