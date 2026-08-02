/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import FiniteDMC.Code
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Achievability for the finite DMC coding theorem

For any rate `R` strictly below capacity and any error tolerance `ε > 0`, block codes of rate at
least `R` and average error at most `ε` exist for all sufficiently large block lengths.

## Main statements

* `FiniteDMC.exists_blockCode_of_lt_mutualInfo` : achievability at a *fixed* input distribution.
* `FiniteDMC.coding_achievability` : achievability below capacity.

## Implementation notes

* **The message-count convention.**  Everywhere in this development the size of the message set is
  compared to `2 ^ (n * R)` by the single real inequality `(2 : ℝ) ^ ((n : ℝ) * R) ≤ c.card`, with
  `c.card : ℕ` coerced to `ℝ` and the power being `Real.rpow`.  No statement mentions a floor or a
  ceiling; `Nat.ceil` may appear inside a construction, but never in a statement.  See `GOAL.md`
  (decision D-8).
* **`exists_blockCode_of_lt_mutualInfo` is an existence statement, not an algorithm.**  Its
  intended proof is the random coding argument: bound the average error *over an ensemble* of
  codebooks, then observe that some realisation is at least as good as the average.  That argument
  yields no procedure for producing the good codebook, and nothing downstream should be phrased as
  if it did.  See `GOAL.md` (decision D-12).
-/

namespace FiniteDMC

open Filter

variable {X Y : Type*} [Fintype X] [Fintype Y] {n : ℕ} {R : ℝ}

/-! ### Facts consumed by achievability -/

/-- A block code with at least `2 ^ (n * R)` messages has rate at least `R`. -/
theorem BlockCode.le_rate_of_rpow_le_card (c : BlockCode X Y n) (hn : 0 < n)
    (h : (2 : ℝ) ^ ((n : ℝ) * R) ≤ c.card) : R ≤ c.rate := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * R) := Real.rpow_pos_of_pos (by norm_num) _
  have hlog : (n : ℝ) * R ≤ Real.logb 2 c.card := by
    calc (n : ℝ) * R = Real.logb 2 ((2 : ℝ) ^ ((n : ℝ) * R)) :=
          (Real.logb_rpow (by norm_num) (by norm_num)).symm
      _ ≤ Real.logb 2 c.card := Real.logb_le_logb_of_le (by norm_num) hpos h
  rw [BlockCode.rate, le_div_iff₀ hn']
  linarith

/-- **Achievability at a fixed input distribution.**  If `R` is strictly below the mutual
information `I(p ; W)`, then for all sufficiently large `n` there is a block code with at least
`2 ^ (n * R)` messages whose average error probability is at most `ε`.

This is the analytic heart of the direct theorem.  It asserts only *existence* of a good code; see
the module docstring. -/
theorem exists_blockCode_of_lt_mutualInfo (W : DMC X Y) (p : PMF X) {ε : ℝ}
    (hR : R < W.mutualInfo p) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ c : BlockCode X Y n,
      (2 : ℝ) ^ ((n : ℝ) * R) ≤ c.card ∧ c.avgError W ≤ ε := by
  sorry

/-! ### The direct theorem -/

/-- **Achievability (direct part) of the channel coding theorem for a finite DMC.**  For every rate
`R` strictly below capacity and every `ε > 0`, block codes of rate at least `R` and average error
probability at most `ε` exist for all sufficiently large block lengths. -/
theorem coding_achievability [Nonempty X] (W : DMC X Y) {ε : ℝ}
    (hR : R < W.capacity) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ c : BlockCode X Y n, R ≤ c.rate ∧ c.avgError W ≤ ε := by
  have hne : (Set.range fun p : PMF X ↦ W.mutualInfo p).Nonempty :=
    ⟨W.mutualInfo (PMF.pure (Classical.arbitrary X)), ⟨_, rfl⟩⟩
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := exists_lt_of_lt_csSup hne hR
  filter_upwards [exists_blockCode_of_lt_mutualInfo W p hp hε, eventually_gt_atTop 0] with
    n hn hpos
  obtain ⟨c, hcard, herr⟩ := hn
  exact ⟨c, c.le_rate_of_rpow_le_card hpos hcard, herr⟩

end FiniteDMC
