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

The converse chain is complete except for single-letterisation: Fano's inequality and the
data-processing step are proved here, and `DMC.mutualInfo_power_le` is the one remaining `sorry`.

## Main statements

* `FiniteDMC.logb_card_le_capacity` : the one-shot Fano bound
  `log₂ |M| ≤ n * C + 1 + Pe * log₂ |M|`.
* `FiniteDMC.BlockCode.rate_mul_one_sub_avgError_le` : the same bound in rate form,
  `rate * (1 - Pe) ≤ C + 1 / n`, which is what both asymptotic statements consume.
* `FiniteDMC.weak_converse` : the weak converse in `R`-form.
* `FiniteDMC.BlockCode.fano_inequality` : Fano's inequality for a block code.
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
open scoped ENNReal

variable {X Y : Type*} [Fintype X] [Fintype Y] {n : ℕ}

/-! ### Facts consumed by the converse -/

/-- Each conditional error probability is at most `1`, being a partial sum of the output law. -/
theorem BlockCode.condError_le_one (c : BlockCode X Y n) (W : DMC X Y) (m : Fin c.card) :
    c.condError W m ≤ 1 := by
  rw [BlockCode.condError]
  calc ∑ y : Fin n → Y, (if c.decode y = m then 0
          else ((W.power n).transition (c.encode m) y).toReal)
      ≤ ∑ y : Fin n → Y, ((W.power n).transition (c.encode m) y).toReal := by
        refine Finset.sum_le_sum fun y _ ↦ ?_
        split
        · exact ENNReal.toReal_nonneg
        · exact le_rfl
    _ = 1 := sum_toReal_eq_one _

/-- The average error probability is at most `1`. -/
theorem BlockCode.avgError_le_one (c : BlockCode X Y n) (W : DMC X Y) : c.avgError W ≤ 1 := by
  have hcard : (0 : ℝ) < c.card := by exact_mod_cast c.card_pos
  have hsum : ∑ m : Fin c.card, c.condError W m ≤ (c.card : ℝ) := by
    calc ∑ m : Fin c.card, c.condError W m ≤ ∑ _m : Fin c.card, (1 : ℝ) :=
          Finset.sum_le_sum fun m _ ↦ c.condError_le_one W m
      _ = (c.card : ℝ) := by simp
  calc c.avgError W ≤ (c.card : ℝ)⁻¹ * (c.card : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hcard)

/-- The average error probability is nonnegative. -/
theorem BlockCode.avgError_nonneg (c : BlockCode X Y n) (W : DMC X Y) : 0 ≤ c.avgError W := by
  rw [BlockCode.avgError]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ ↦ ?_)
  rw [BlockCode.condError]
  refine Finset.sum_nonneg fun y _ ↦ ?_
  split
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

/-- The rate of a block code is nonnegative, since it has at least one message. -/
theorem BlockCode.rate_nonneg (c : BlockCode X Y n) : 0 ≤ c.rate := by
  rw [BlockCode.rate]
  refine div_nonneg (Real.logb_nonneg one_lt_two ?_) (Nat.cast_nonneg n)
  exact_mod_cast c.card_pos

/-- The entropy of the uniform message law is `log₂ |M|`. -/
theorem BlockCode.entropy_messageDist (c : BlockCode X Y n) :
    entropy c.messageDist = Real.logb 2 c.card := by
  haveI := c.nonempty_fin
  have hcard : (0 : ℝ) < c.card := by exact_mod_cast c.card_pos
  rw [entropy]
  simp only [BlockCode.messageDist, PMF.uniformOfFintype_apply, Fintype.card_fin,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Real.logb_inv]
  field_simp

/-- The message marginal of the joint message-output law is the uniform message law. -/
theorem BlockCode.msgOutJoint_map_fst (c : BlockCode X Y n) (W : DMC X Y) :
    (c.msgOutJoint W).map Prod.fst = c.messageDist :=
  DMC.joint_map_fst _ _

/-- The total mass the joint law puts on decoding errors is exactly the average error
probability. -/
theorem BlockCode.sum_error_mass (c : BlockCode X Y n) (W : DMC X Y) :
    ∑ z : Fin c.card × (Fin n → Y),
      (if z.1 = c.decode z.2 then 0 else ((c.msgOutJoint W) z).toReal) = c.avgError W := by
  rw [Fintype.sum_prod_type, BlockCode.avgError, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [BlockCode.condError, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [c.msgOutJoint_apply W, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  by_cases h : c.decode y = m
  · simp [h]
  · simp [h, Ne.symm h]

/-- **Fano's inequality**, specialised to a block code: the residual uncertainty about the message
given the channel output is controlled by the average error probability.

The `1` on the right is the usual crude bound `h₂(Pe) ≤ 1` for the binary entropy of `Pe`. -/
theorem BlockCode.fano_inequality (c : BlockCode X Y n) (W : DMC X Y) :
    condEntropy (c.msgOutJoint W) ≤ 1 + c.avgError W * Real.logb 2 c.card := by
  classical
  have hK1 : (1 : ℝ) ≤ (c.card : ℝ) := by exact_mod_cast c.card_pos
  set μ := c.msgOutJoint W with hμdef
  set ν := μ.map Prod.snd with hνdef
  set b : ℝ := 1 / (2 * ((c.card : ℝ) - 1)) with hbdef
  set r : Fin c.card × (Fin n → Y) → ℝ :=
    fun z ↦ if z.1 = c.decode z.2 then 1 / 2 else b with hrdef
  -- A decoding error is only possible when there are at least two messages.
  have htwo : ∀ m : Fin c.card, ∀ y : Fin n → Y, m ≠ c.decode y → (2 : ℝ) ≤ (c.card : ℝ) := by
    intro m y hz
    haveI : Nontrivial (Fin c.card) := ⟨⟨m, c.decode y, hz⟩⟩
    have h : 1 < c.card := by
      rw [← Fintype.card_fin c.card]
      exact Fintype.one_lt_card_iff_nontrivial.mpr ‹_›
    exact_mod_cast h
  have hrpos : ∀ z : Fin c.card × (Fin n → Y), 0 < r z := by
    rintro ⟨m, y⟩
    rw [hrdef]
    by_cases h : m = c.decode y
    · simp [h]
    · have h2 := htwo m y h
      have hpos : (0 : ℝ) < 2 * ((c.card : ℝ) - 1) := by linarith
      simp only [h, if_false]
      exact div_pos one_pos hpos
  have hμle : ∀ z : Fin c.card × (Fin n → Y), μ z ≤ ν z.2 := by
    rintro ⟨m, y⟩; exact le_map_snd μ m y
  -- The reference weight.
  have hwnonneg : ∀ z, 0 ≤ (ν z.2).toReal * r z := fun z ↦
    mul_nonneg ENNReal.toReal_nonneg (hrpos z).le
  have hrsum : ∀ y : Fin n → Y, ∑ m : Fin c.card, r (m, y) ≤ 1 := by
    intro y
    have hsplit : ∑ m : Fin c.card, r (m, y) = ((c.card : ℝ) - 1) * b + 1 / 2 := by
      have hpt : ∀ m : Fin c.card, r (m, y) = b + (if m = c.decode y then 1 / 2 - b else 0) := by
        intro m; rw [hrdef]; by_cases h : m = c.decode y <;> simp [h]
      rw [Finset.sum_congr rfl fun m _ ↦ hpt m, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Finset.sum_ite_eq' Finset.univ (c.decode y) fun _ ↦ (1 : ℝ) / 2 - b]
      simp
      ring
    rw [hsplit]
    rcases eq_or_lt_of_le hK1 with h | h
    · rw [← h]; norm_num
    · have hc : (0 : ℝ) < (c.card : ℝ) - 1 := by linarith
      have : ((c.card : ℝ) - 1) * b = 1 / 2 := by rw [hbdef]; field_simp
      rw [this]; norm_num
  have hsumw : ∑ z : Fin c.card × (Fin n → Y), (ν z.2).toReal * r z ≤ 1 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc ∑ y : Fin n → Y, ∑ m : Fin c.card, (ν y).toReal * r (m, y)
        = ∑ y : Fin n → Y, (ν y).toReal * ∑ m : Fin c.card, r (m, y) := by
          exact Finset.sum_congr rfl fun y _ ↦ (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ y : Fin n → Y, (ν y).toReal * 1 :=
          Finset.sum_le_sum fun y _ ↦
            mul_le_mul_of_nonneg_left (hrsum y) ENNReal.toReal_nonneg
      _ = 1 := by simp [sum_toReal_eq_one]
  have hac : ∀ z, (ν z.2).toReal * r z = 0 → μ z = 0 := by
    intro z hz
    have hν0 : (ν z.2).toReal = 0 := by
      rcases mul_eq_zero.1 hz with h | h
      · exact h
      · exact absurd h (ne_of_gt (hrpos z))
    have : ν z.2 = 0 := by
      rwa [ENNReal.toReal_eq_zero_iff, or_iff_left (ν.apply_ne_top _)] at hν0
    exact le_antisymm (this ▸ hμle z) _root_.zero_le
  -- Gibbs against that weight.
  have hgibbs := entropy_le_neg_sum_mul_logb μ (fun z ↦ (ν z.2).toReal * r z) hwnonneg hsumw hac
  have hsplitlog : ∀ z : Fin c.card × (Fin n → Y),
      (μ z).toReal * Real.logb 2 ((ν z.2).toReal * r z)
      = (μ z).toReal * Real.logb 2 (ν z.2).toReal + (μ z).toReal * Real.logb 2 (r z) := by
    intro z
    rcases eq_or_lt_of_le (ENNReal.toReal_nonneg : (0 : ℝ) ≤ (μ z).toReal) with hz | hz
    · rw [← hz]; ring
    · have hμne : μ z ≠ 0 := by intro h; rw [h] at hz; simp at hz
      have hνne : ν z.2 ≠ 0 := fun h ↦ hμne (le_antisymm (h ▸ hμle z) _root_.zero_le)
      have hν0 : (0 : ℝ) < (ν z.2).toReal := ENNReal.toReal_pos hνne (ν.apply_ne_top _)
      rw [Real.logb, Real.logb, Real.logb, Real.log_mul (ne_of_gt hν0) (ne_of_gt (hrpos z))]
      ring
  have hpart1 : ∑ z : Fin c.card × (Fin n → Y), (μ z).toReal * Real.logb 2 (ν z.2).toReal
      = -entropy ν := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, entropy, neg_neg]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    dsimp only
    rw [← Finset.sum_mul]
    congr 1
    rw [hνdef, map_snd_apply, ENNReal.toReal_sum]
    intro a _
    exact μ.apply_ne_top _
  have hterm : ∀ z : Fin c.card × (Fin n → Y),
      -((μ z).toReal * Real.logb 2 (r z))
      = (μ z).toReal + Real.logb 2 ((c.card : ℝ) - 1)
          * (if z.1 = c.decode z.2 then 0 else (μ z).toReal) := by
    rintro ⟨m, y⟩
    dsimp only
    have hl2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
    by_cases h : m = c.decode y
    · have hr : r (m, y) = 1 / 2 := by rw [hrdef]; simp [h]
      have hlog : Real.logb 2 ((1 : ℝ) / 2) = -1 := by
        rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.logb, Real.log_inv]
        field_simp
      rw [hr, hlog, if_pos h]
      ring
    · have h2 := htwo m y h
      have hc : (0 : ℝ) < (c.card : ℝ) - 1 := by linarith
      have hr : r (m, y) = 1 / (2 * ((c.card : ℝ) - 1)) := by rw [hrdef]; simp [h, hbdef]
      have hlog : Real.logb 2 (1 / (2 * ((c.card : ℝ) - 1)))
          = -(1 + Real.logb 2 ((c.card : ℝ) - 1)) := by
        rw [one_div, Real.logb_inv, Real.logb, Real.log_mul (by norm_num) (ne_of_gt hc),
          Real.logb]
        field_simp
      rw [hr, hlog, if_neg h]
      ring
  have hpart2 : -∑ z : Fin c.card × (Fin n → Y), (μ z).toReal * Real.logb 2 (r z)
      = 1 + c.avgError W * Real.logb 2 ((c.card : ℝ) - 1) := by
    rw [← Finset.sum_neg_distrib, Finset.sum_congr rfl fun z _ ↦ hterm z,
      Finset.sum_add_distrib, sum_toReal_eq_one, ← Finset.mul_sum, c.sum_error_mass W]
    ring
  have hmono : Real.logb 2 ((c.card : ℝ) - 1) ≤ Real.logb 2 (c.card : ℝ) := by
    rcases eq_or_lt_of_le hK1 with h | h
    · rw [← h]; norm_num
    · exact Real.logb_le_logb_of_le one_lt_two (by linarith) (by linarith)
  have hPe := c.avgError_nonneg W
  rw [Finset.sum_congr rfl fun z _ ↦ hsplitlog z, Finset.sum_add_distrib, hpart1] at hgibbs
  rw [condEntropy, ← hνdef]
  nlinarith [mul_le_mul_of_nonneg_left hmono hPe, hpart2]

/-- **Data processing inequality** for the Markov chain `M → Xⁿ → Yⁿ` induced by a block code:
the encoder cannot increase the information the output carries about the message. -/
theorem BlockCode.mutualInfo_msgOutJoint_le (c : BlockCode X Y n) (W : DMC X Y) :
    mutualInfo (c.msgOutJoint W) ≤ mutualInfo (c.inOutJoint W) := by
  classical
  refine le_of_eq ?_
  change (c.codeChannel W).mutualInfo c.messageDist
      = (W.power n).mutualInfo (c.messageDist.map c.encode)
  rw [DMC.mutualInfo_eq, DMC.mutualInfo_eq]
  congr 1
  · congr 1
    exact (PMF.bind_map c.messageDist c.encode (W.power n).transition).symm
  · exact (sum_map_toReal_mul c.messageDist c.encode
      fun x ↦ entropy ((W.power n).transition x)).symm

/-- **Single-letterisation**: `n` uses of a memoryless channel carry at most `n * C` bits,
whatever the joint law of the input block. -/
theorem DMC.mutualInfo_power_le (W : DMC X Y) (n : ℕ) (q : PMF (Fin n → X)) :
    (W.power n).mutualInfo q ≤ n * W.capacity := by
  classical
  rw [DMC.mutualInfo_eq]
  have hcond : ∑ x : Fin n → X, (q x).toReal * entropy ((W.power n).transition x)
      = ∑ i : Fin n, ∑ a : X, ((q.map fun x ↦ x i) a).toReal * entropy (W.transition a) := by
    calc ∑ x : Fin n → X, (q x).toReal * entropy ((W.power n).transition x)
        = ∑ x : Fin n → X, ∑ i : Fin n, (q x).toReal * entropy (W.transition (x i)) := by
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          rw [entropy_power_transition, Finset.mul_sum]
      _ = ∑ i : Fin n, ∑ x : Fin n → X, (q x).toReal * entropy (W.transition (x i)) :=
          Finset.sum_comm
      _ = ∑ i : Fin n, ∑ a : X, ((q.map fun x ↦ x i) a).toReal * entropy (W.transition a) :=
          Finset.sum_congr rfl fun i _ ↦
            (sum_map_toReal_mul q (fun x ↦ x i) fun a ↦ entropy (W.transition a)).symm
  have hout : entropy (q.bind (W.power n).transition)
      ≤ ∑ i : Fin n, entropy ((q.map fun x ↦ x i).bind W.transition) := by
    calc entropy (q.bind (W.power n).transition)
        ≤ ∑ i : Fin n, entropy ((q.bind (W.power n).transition).map fun y ↦ y i) :=
          entropy_le_sum_entropy_proj _
      _ = ∑ i : Fin n, entropy ((q.map fun x ↦ x i).bind W.transition) :=
          Finset.sum_congr rfl fun i _ ↦ by rw [power_bind_map_proj]
  rw [hcond]
  calc entropy (q.bind (W.power n).transition)
        - ∑ i : Fin n, ∑ a : X, ((q.map fun x ↦ x i) a).toReal * entropy (W.transition a)
      ≤ ∑ i : Fin n, entropy ((q.map fun x ↦ x i).bind W.transition)
        - ∑ i : Fin n, ∑ a : X, ((q.map fun x ↦ x i) a).toReal * entropy (W.transition a) := by
        linarith
    _ = ∑ i : Fin n, W.mutualInfo (q.map fun x ↦ x i) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ (DMC.mutualInfo_eq W _).symm
    _ ≤ ∑ _i : Fin n, W.capacity := Finset.sum_le_sum fun i _ ↦ W.mutualInfo_le_capacity _
    _ = n * W.capacity := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

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
  obtain ⟨B, hB⟩ := hbdd
  have hle : ∀ n, (codes n).rate ≤ B := fun n ↦ hB ⟨n, rfl⟩
  have hcob : IsCoboundedUnder (· ≤ ·) atTop fun n ↦ (codes n).rate :=
    isCoboundedUnder_le_of_le atTop fun n ↦ (codes n).rate_nonneg
  have htend : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) + B * (codes n).avgError W) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ B) atTop (𝓝 B) := tendsto_const_nhds
    have h2 : Tendsto (fun n : ℕ ↦ B * (codes n).avgError W) atTop (𝓝 0) := by
      simpa using hconst.mul herr
    simpa using tendsto_one_div_atTop_nhds_zero_nat.add h2
  refine le_of_forall_pos_le_add fun ε hε ↦ limsup_le_of_le hcob ?_
  filter_upwards [eventually_gt_atTop 0, htend.eventually (gt_mem_nhds hε)] with n hn hlt
  have hbase := (codes n).rate_mul_one_sub_avgError_le W hn
  have hpe := (codes n).avgError_nonneg W
  nlinarith [mul_le_mul_of_nonneg_right (hle n) hpe]

end FiniteDMC
