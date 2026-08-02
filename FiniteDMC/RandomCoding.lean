/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import FiniteDMC.Code

/-!
# The random-coding layer

Infrastructure for the direct theorem, and the decomposition of achievability into two named
obligations.

## Main definitions

* `PMF.pi` : the product of a finite family of probability mass functions.  Mathlib has no such
  construction; this development needs it for the i.i.d. input law and for the codebook ensemble.
* `FiniteDMC.DMC.infoDensity` : the information density `i(x ; y) = log₂ (W(y ∣ x) / P_Y(y))`.
* `FiniteDMC.DMC.spectrumTail` : the probability that the `n`-letter information density fails to
  exceed a threshold.

## Main statements

* `FiniteDMC.exists_le_of_sum_toReal_mul_le` : some realisation is at least as good as the
  average.  This is the step that makes random coding non-constructive (D-12).
* `FiniteDMC.DMC.sum_joint_infoDensity` : the mean of the information density is the mutual
  information -- the bridge between D-5 and the quantity achievability concentrates.

## Implementation notes

**The route.**  Achievability is decomposed along the *information-density threshold decoding*
route rather than the textbook joint-typicality route.  A joint-typicality argument needs three
simultaneous concentration estimates; threshold decoding needs exactly one, namely
`tendsto_spectrumTail`, and no typicality set at all.  This is a formalisation choice, not a
mathematical one; see `HARD-PARTS.md`.

**`PMF.pi` may clash.**  If Mathlib later gains a product of `PMF`s under this name, this
declaration should be deleted rather than renamed.
-/

open Finset
open scoped ENNReal

namespace PMF

/-- The product mass function over a finite index is normalised. -/
theorem pi_sum_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : Type*} [Fintype Z]
    (m : ι → PMF Z) : ∑ z : ι → Z, ∏ i, m i (z i) = 1 := by
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun i _ ↦ FiniteDMC.sum_coe_eq_one (m i)

/-- The product of a finite family of probability mass functions. -/
noncomputable def pi {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : Type*} [Fintype Z]
    (m : ι → PMF Z) : PMF (ι → Z) :=
  PMF.ofFintype (fun z ↦ ∏ i, m i (z i)) (pi_sum_eq_one m)

@[simp]
theorem pi_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : Type*} [Fintype Z]
    (m : ι → PMF Z) (z : ι → Z) : pi m z = ∏ i, m i (z i) := rfl

end PMF

namespace FiniteDMC

open Filter Topology

variable {ι : Type*} [Fintype ι]

/-- **Some realisation is at least as good as the average.**  If a weighted average of `f` over a
distribution `μ` is at most `b`, then some point of the support of `μ` has `f` at most `b`.

This is the step that makes random coding non-constructive: it produces a good codebook without
producing any way to find one.  See `GOAL.md` (decision D-12). -/
theorem exists_le_of_sum_toReal_mul_le (μ : PMF ι) (f : ι → ℝ) {b : ℝ}
    (h : ∑ i, (μ i).toReal * f i ≤ b) : ∃ i, μ i ≠ 0 ∧ f i ≤ b := by
  classical
  by_contra hcon
  have hgt : ∀ i, μ i ≠ 0 → b < f i := by
    intro i hi
    by_contra hle
    exact hcon ⟨i, hi, not_lt.1 hle⟩
  set S : Finset ι := Finset.univ.filter fun i ↦ μ i ≠ 0 with hS
  have hmemS : ∀ i, i ∈ S ↔ μ i ≠ 0 := by
    intro i; rw [hS, Finset.mem_filter]; exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ i, h⟩⟩
  have hzero : ∀ i ∈ Finset.univ, i ∉ S → μ i = 0 := by
    intro i _ hi
    by_contra hne
    exact hi ((hmemS i).2 hne)
  have hmass : ∑ i ∈ S, (μ i).toReal = 1 :=
    (Finset.sum_subset (Finset.subset_univ S)
      (fun i hi hi' ↦ by rw [hzero i hi hi']; simp)).trans (sum_toReal_eq_one μ)
  have hsum : ∑ i, (μ i).toReal * f i = ∑ i ∈ S, (μ i).toReal * f i :=
    (Finset.sum_subset (Finset.subset_univ S)
      (fun i hi hi' ↦ by rw [hzero i hi hi']; simp)).symm
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.sum_empty] at hmass
    exact zero_ne_one hmass
  have hlt : ∑ i ∈ S, (μ i).toReal * b < ∑ i ∈ S, (μ i).toReal * f i :=
    Finset.sum_lt_sum_of_nonempty hne fun i hi ↦
      mul_lt_mul_of_pos_left (hgt i ((hmemS i).1 hi))
        (ENNReal.toReal_pos ((hmemS i).1 hi) (μ.apply_ne_top i))
  rw [← Finset.sum_mul, hmass, one_mul] at hlt
  rw [hsum] at h
  linarith

variable {X Y : Type*} [Fintype X] [Fintype Y] {R : ℝ}

/-- The information density `i(x ; y) = log₂ (W(y ∣ x) / P_Y(y))`.

**Caution.**  `Real.logb` sends `0` to the junk value `0`, so when `W(y ∣ x) = 0` and `P_Y(y) > 0`
this evaluates to `0` where information theory requires `-∞`.  That is harmless *under the joint
law*, which puts no mass on such pairs, and every use here is under the joint.  It is **not**
harmless under a product of marginals, which is why `sum_ite_lt_le_rpow_neg` is stated as an
inequality between masses rather than through this function.  See `HARD-PARTS.md`. -/
noncomputable def DMC.infoDensity (W : DMC X Y) (p : PMF X) (x : X) (y : Y) : ℝ :=
  Real.logb 2 ((W.transition x y).toReal / ((p.bind W.transition) y).toReal)

theorem DMC.le_outputDist (W : DMC X Y) (p : PMF X) (x : X) (y : Y) :
    p x * W.transition x y ≤ (p.bind W.transition) y := by
  rw [PMF.bind_apply, tsum_fintype]
  exact Finset.single_le_sum (f := fun x' ↦ p x' * W.transition x' y)
    (fun i _ ↦ _root_.zero_le) (Finset.mem_univ x)

/-- **The mean of the information density is the mutual information.**  This is the bridge between
the inclusion-exclusion definition of `mutualInfo` (D-5) and the quantity that the achievability
argument actually concentrates. -/
theorem DMC.sum_joint_infoDensity (W : DMC X Y) (p : PMF X) :
    ∑ z : X × Y, ((W.joint p) z).toReal * W.infoDensity p z.1 z.2 = W.mutualInfo p := by
  classical
  have hPY : ∀ y : Y, ((p.bind W.transition) y).toReal
      = ∑ x, (p x).toReal * (W.transition x y).toReal := by
    intro y
    rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum fun x _ ↦
      ENNReal.mul_ne_top (p.apply_ne_top x) ((W.transition x).apply_ne_top y)]
    exact Finset.sum_congr rfl fun x _ ↦ ENNReal.toReal_mul
  have hsplit : ∀ (x : X) (y : Y),
      ((W.joint p) (x, y)).toReal * W.infoDensity p x y
      = (p x).toReal * ((W.transition x y).toReal * Real.logb 2 (W.transition x y).toReal)
        - (p x).toReal * (W.transition x y).toReal
            * Real.logb 2 ((p.bind W.transition) y).toReal := by
    intro x y
    rw [DMC.joint_apply, ENNReal.toReal_mul, DMC.infoDensity]
    rcases eq_or_lt_of_le (mul_nonneg (ENNReal.toReal_nonneg : (0:ℝ) ≤ (p x).toReal)
        (ENNReal.toReal_nonneg : (0:ℝ) ≤ (W.transition x y).toReal)) with h | h
    · rw [← h]
      have hz : (p x).toReal * (W.transition x y).toReal = 0 := h.symm
      rcases mul_eq_zero.1 hz with h1 | h1 <;> rw [h1] <;> ring
    · have ha : (0 : ℝ) < (W.transition x y).toReal := by
        by_contra hc
        rw [le_antisymm (not_lt.1 hc) ENNReal.toReal_nonneg] at h
        simp at h
      have hc : (0 : ℝ) < ((p.bind W.transition) y).toReal := by
        have hle := ENNReal.toReal_mono ((p.bind W.transition).apply_ne_top y)
          (DMC.le_outputDist W p x y)
        rw [ENNReal.toReal_mul] at hle
        linarith
      rw [Real.logb, Real.logb, Real.logb, Real.log_div (ne_of_gt ha) (ne_of_gt hc)]
      ring
  have hA : ∑ x : X, ∑ y : Y, (p x).toReal * ((W.transition x y).toReal
        * Real.logb 2 (W.transition x y).toReal)
      = -∑ x : X, (p x).toReal * entropy (W.transition x) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← Finset.mul_sum, entropy]
    ring
  have hB : ∑ x : X, ∑ y : Y, (p x).toReal * (W.transition x y).toReal
        * Real.logb 2 ((p.bind W.transition) y).toReal
      = -entropy (p.bind W.transition) := by
    rw [Finset.sum_comm, entropy, neg_neg]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [← Finset.sum_mul, ← hPY]
  rw [Fintype.sum_prod_type]
  simp only [hsplit]
  rw [show ∀ (F G : X → Y → ℝ), ∑ x : X, ∑ y : Y, (F x y - G x y)
        = (∑ x : X, ∑ y : Y, F x y) - ∑ x : X, ∑ y : Y, G x y from fun F G ↦ by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_sub_distrib (F x) (G x)]
  rw [hA, hB, DMC.mutualInfo_eq]
  ring

/-- The joint law of input and output blocks under an i.i.d. input law. -/
noncomputable def DMC.jointPow (W : DMC X Y) (p : PMF X) (n : ℕ) :
    PMF ((Fin n → X) × (Fin n → Y)) :=
  (W.power n).joint (PMF.pi fun _ : Fin n ↦ p)

/-- The `n`-letter information density, a sum of per-coordinate information densities. -/
noncomputable def DMC.infoDensityPow (W : DMC X Y) (p : PMF X) (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) : ℝ := ∑ i, W.infoDensity p (x i) (y i)

/-- The information-spectrum tail: the probability that the `n`-letter information density fails
to exceed the threshold `τ`. -/
noncomputable def DMC.spectrumTail (W : DMC X Y) (p : PMF X) (n : ℕ) (τ : ℝ) : ℝ :=
  ∑ z : (Fin n → X) × (Fin n → Y),
    if W.infoDensityPow p n z.1 z.2 ≤ τ then ((W.jointPow p n) z).toReal else 0

theorem DMC.jointPow_apply (W : DMC X Y) (p : PMF X) (n : ℕ) (x : Fin n → X) (y : Fin n → Y) :
    W.jointPow p n (x, y) = ∏ i, (W.joint p) (x i, y i) := by
  rw [DMC.jointPow, DMC.joint_apply]
  simp only [PMF.pi_apply, DMC.power_transition_apply, DMC.joint_apply]
  rw [← Finset.prod_mul_distrib]

/-- The spectrum tail, transported to the i.i.d. product over `Fin n → X × Y`. -/
theorem spectrumTail_eq (W : DMC X Y) (p : PMF X) (n : ℕ) (τ : ℝ) :
    W.spectrumTail p n τ
      = ∑ w : Fin n → X × Y,
          if (∑ i, W.infoDensity p (w i).1 (w i).2) ≤ τ
          then ∏ i, ((W.joint p) (w i)).toReal else 0 := by
  rw [DMC.spectrumTail]
  refine (Fintype.sum_equiv
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ ↦ X) fun _ ↦ Y) _ _ ?_).symm
  intro w
  simp [DMC.infoDensityPow, DMC.jointPow_apply, ENNReal.toReal_prod,
    Equiv.arrowProdEquivProdArrow]

/-- **Variance of an i.i.d. sum.**  If `g` is centred under `μ`, the second moment of
`∑ i, g (w i)` under the `n`-fold product of `μ` is `n` times the second moment of `g`. -/
theorem sum_prod_sq {Z : Type*} [Fintype Z] (μ : PMF Z) (g : Z → ℝ)
    (hcent : ∑ a, (μ a).toReal * g a = 0) (n : ℕ) :
    ∑ w : Fin n → Z, (∏ i, (μ (w i)).toReal) * (∑ i, g (w i)) ^ 2
      = n * ∑ a, (μ a).toReal * (g a) ^ 2 := by
  classical
  have hmass : ∑ a : Z, (μ a).toReal = 1 := sum_toReal_eq_one μ
  calc ∑ w : Fin n → Z, (∏ i, (μ (w i)).toReal) * (∑ i, g (w i)) ^ 2
      = ∑ w : Fin n → Z, ∑ i : Fin n, ∑ j : Fin n,
          (∏ k, (μ (w k)).toReal) * (g (w i) * g (w j)) := by
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ Finset.mul_sum _ _ _
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ w : Fin n → Z,
          (∏ k, (μ (w k)).toReal) * (g (w i) * g (w j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
    _ = ∑ _i : Fin n, ∑ j : Fin n,
          (if _i = j then ∑ a, (μ a).toReal * (g a) ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl]
          have h := sum_prod_mul (fun (_ : Fin n) (a : Z) ↦ (μ a).toReal)
            (fun _ ↦ hmass) i fun a ↦ g a * g a
          simpa [pow_two] using h
        · rw [if_neg hij, sum_prod_mul_two (fun (_ : Fin n) (a : Z) ↦ (μ a).toReal)
            (fun _ ↦ hmass) hij g g, hcent, mul_zero]
    _ = n * ∑ a, (μ a).toReal * (g a) ^ 2 := by
        simp [Finset.sum_ite_eq, Finset.card_univ]

/-- **Chebyshev's inequality** for the information spectrum. -/
theorem spectrumTail_le (W : DMC X Y) (p : PMF X) {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) :
    W.spectrumTail p n ((n : ℝ) * (W.mutualInfo p - δ))
      ≤ (∑ a : X × Y, ((W.joint p) a).toReal
          * (W.infoDensity p a.1 a.2 - W.mutualInfo p) ^ 2) / ((n : ℝ) * δ ^ 2) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hd : (0 : ℝ) < ((n : ℝ) * δ) ^ 2 := by positivity
  have hmass : ∑ a : X × Y, ((W.joint p) a).toReal = 1 := sum_toReal_eq_one _
  have hcent : ∑ a : X × Y, ((W.joint p) a).toReal
      * (W.infoDensity p a.1 a.2 - W.mutualInfo p) = 0 := by
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, W.sum_joint_infoDensity p, ← Finset.sum_mul, hmass, one_mul,
      sub_self]
  have hvar := sum_prod_sq (W.joint p) (fun a ↦ W.infoDensity p a.1 a.2 - W.mutualInfo p) hcent n
  rw [spectrumTail_eq]
  have hterm : ∀ w : Fin n → X × Y,
      (if (∑ i, W.infoDensity p (w i).1 (w i).2) ≤ (n : ℝ) * (W.mutualInfo p - δ)
        then ∏ i, ((W.joint p) (w i)).toReal else 0)
      ≤ (∏ i, ((W.joint p) (w i)).toReal)
          * (∑ i, (W.infoDensity p (w i).1 (w i).2 - W.mutualInfo p)) ^ 2
          / ((n : ℝ) * δ) ^ 2 := by
    intro w
    have hP : 0 ≤ ∏ i, ((W.joint p) (w i)).toReal :=
      Finset.prod_nonneg fun i _ ↦ ENNReal.toReal_nonneg
    have hgsum : ∑ i, (W.infoDensity p (w i).1 (w i).2 - W.mutualInfo p)
        = (∑ i, W.infoDensity p (w i).1 (w i).2) - n * W.mutualInfo p := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    split
    · next hle =>
      have hs : ∑ i, (W.infoDensity p (w i).1 (w i).2 - W.mutualInfo p) ≤ -((n : ℝ) * δ) := by
        rw [hgsum]; nlinarith
      have hsq : ((n : ℝ) * δ) ^ 2
          ≤ (∑ i, (W.infoDensity p (w i).1 (w i).2 - W.mutualInfo p)) ^ 2 := by
        nlinarith [hs, mul_pos hn' hδ]
      rw [le_div_iff₀ hd]
      nlinarith [hP, hsq]
    · positivity
  calc ∑ w : Fin n → X × Y,
        (if (∑ i, W.infoDensity p (w i).1 (w i).2) ≤ (n : ℝ) * (W.mutualInfo p - δ)
          then ∏ i, ((W.joint p) (w i)).toReal else 0)
      ≤ ∑ w : Fin n → X × Y, (∏ i, ((W.joint p) (w i)).toReal)
          * (∑ i, (W.infoDensity p (w i).1 (w i).2 - W.mutualInfo p)) ^ 2
          / ((n : ℝ) * δ) ^ 2 := Finset.sum_le_sum fun w _ ↦ hterm w
    _ = ((n : ℝ) * ∑ a : X × Y, ((W.joint p) a).toReal
          * (W.infoDensity p a.1 a.2 - W.mutualInfo p) ^ 2) / ((n : ℝ) * δ) ^ 2 := by
        rw [← Finset.sum_div, hvar]
    _ = (∑ a : X × Y, ((W.joint p) a).toReal
          * (W.infoDensity p a.1 a.2 - W.mutualInfo p) ^ 2) / ((n : ℝ) * δ ^ 2) := by
        field_simp

/-- The output law of the block channel under an i.i.d. input. -/
noncomputable def DMC.outputPow (W : DMC X Y) (p : PMF X) (n : ℕ) : PMF (Fin n → Y) :=
  (PMF.pi fun _ : Fin n ↦ p).bind (W.power n).transition

/-- The i.i.d. input law and the block transition law recover the block joint. -/
theorem DMC.jointPow_toReal (W : DMC X Y) (p : PMF X) (n : ℕ)
    (z : (Fin n → X) × (Fin n → Y)) :
    (W.jointPow p n z).toReal
      = ((PMF.pi fun _ : Fin n ↦ p) z.1).toReal
        * ((W.power n).transition z.1 z.2).toReal := by
  obtain ⟨x, y⟩ := z
  rw [DMC.jointPow, DMC.joint_apply, ENNReal.toReal_mul]

/-- **Change of measure.**  Under the *product of the marginals* — an independent codeword paired
with the received block — the probability that the likelihood ratio exceeds `2 ^ τ` is at most
`2 ^ (-τ)`.

This is stated as an inequality between masses rather than through the information density, and
deliberately so: `Real.logb` sends `0` to the junk value `0`, whereas the information density of a
pair with `W(y ∣ x) = 0` must behave as `-∞` for this bound to hold. -/
theorem sum_ite_lt_le_rpow_neg (W : DMC X Y) (p : PMF X) (n : ℕ) (τ : ℝ) :
    ∑ z : (Fin n → X) × (Fin n → Y),
      (if (2 : ℝ) ^ τ * ((W.outputPow p n) z.2).toReal
            < ((W.power n).transition z.1 z.2).toReal
        then ((PMF.pi fun _ : Fin n ↦ p) z.1).toReal * ((W.outputPow p n) z.2).toReal
        else 0)
      ≤ (2 : ℝ) ^ (-τ) := by
  classical
  have h2 : (0 : ℝ) < (2 : ℝ) ^ τ := Real.rpow_pos_of_pos (by norm_num) _
  have hjoint : ∑ z : (Fin n → X) × (Fin n → Y),
      ((PMF.pi fun _ : Fin n ↦ p) z.1).toReal
        * ((W.power n).transition z.1 z.2).toReal = 1 := by
    rw [← sum_toReal_eq_one (W.jointPow p n)]
    exact (Finset.sum_congr rfl fun z _ ↦ W.jointPow_toReal p n z).symm
  calc ∑ z : (Fin n → X) × (Fin n → Y),
        (if (2 : ℝ) ^ τ * ((W.outputPow p n) z.2).toReal
              < ((W.power n).transition z.1 z.2).toReal
          then ((PMF.pi fun _ : Fin n ↦ p) z.1).toReal * ((W.outputPow p n) z.2).toReal
          else 0)
      ≤ ∑ z : (Fin n → X) × (Fin n → Y), (2 : ℝ) ^ (-τ) *
          (((PMF.pi fun _ : Fin n ↦ p) z.1).toReal
            * ((W.power n).transition z.1 z.2).toReal) := by
        refine Finset.sum_le_sum fun z _ ↦ ?_
        have hp : (0 : ℝ) ≤ ((PMF.pi fun _ : Fin n ↦ p) z.1).toReal := ENNReal.toReal_nonneg
        split
        · next hlt =>
          have hkey : ((W.outputPow p n) z.2).toReal
              ≤ (2 : ℝ) ^ (-τ) * ((W.power n).transition z.1 z.2).toReal := by
            rw [Real.rpow_neg (by norm_num), inv_mul_eq_div, le_div_iff₀ h2]
            nlinarith [hlt]
          nlinarith [hkey, hp]
        · have : (0 : ℝ) ≤ (2 : ℝ) ^ (-τ) := (Real.rpow_pos_of_pos (by norm_num) _).le
          positivity
    _ = (2 : ℝ) ^ (-τ) * 1 := by rw [← Finset.mul_sum, hjoint]
    _ = (2 : ℝ) ^ (-τ) := mul_one _

/-- **The output of a memoryless channel under an i.i.d. input is i.i.d.** -/
theorem DMC.outputPow_apply (W : DMC X Y) (p : PMF X) (n : ℕ) (y : Fin n → Y) :
    (W.outputPow p n) y = ∏ i, (p.bind W.transition) (y i) := by
  classical
  rw [DMC.outputPow, PMF.bind_apply, tsum_fintype]
  have h1 : ∀ x : Fin n → X, (PMF.pi fun _ : Fin n ↦ p) x * (W.power n).transition x y
      = ∏ i, (p (x i) * W.transition (x i) (y i)) := by
    intro x
    rw [PMF.pi_apply, DMC.power_transition_apply, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun x _ ↦ h1 x,
    ← Fintype.prod_sum fun (i : Fin n) (a : X) ↦ p a * W.transition a (y i)]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [PMF.bind_apply, tsum_fintype]

/-- On the support of the joint law, the `n`-letter information density really is the logarithm of
the likelihood ratio.  This is the bridge between the log-sum form, which the weak law needs, and
the mass form, which the decoder needs. -/
theorem infoDensityPow_eq_logb (W : DMC X Y) (p : PMF X) (n : ℕ)
    {x : Fin n → X} {y : Fin n → Y} (h : W.jointPow p n (x, y) ≠ 0) :
    W.infoDensityPow p n x y
      = Real.logb 2 (((W.power n).transition x y).toReal / ((W.outputPow p n) y).toReal) := by
  classical
  have hmul : (PMF.pi fun _ : Fin n ↦ p) x * (W.power n).transition x y ≠ 0 := by
    rw [DMC.jointPow, DMC.joint_apply] at h; exact h
  have hpx : (PMF.pi fun _ : Fin n ↦ p) x ≠ 0 := fun hz ↦ hmul (by rw [hz, zero_mul])
  have hWy : (W.power n).transition x y ≠ 0 := fun hz ↦ hmul (by rw [hz, mul_zero])
  have hp : ∀ i, p (x i) ≠ 0 := fun i hz ↦ hpx (by
    rw [PMF.pi_apply]; exact Finset.prod_eq_zero (Finset.mem_univ i) hz)
  have hW : ∀ i, W.transition (x i) (y i) ≠ 0 := fun i hz ↦ hWy (by
    rw [DMC.power_transition_apply]; exact Finset.prod_eq_zero (Finset.mem_univ i) hz)
  have hc : ∀ i, (0 : ℝ) < ((p.bind W.transition) (y i)).toReal := by
    intro i
    refine ENNReal.toReal_pos ?_ ((p.bind W.transition).apply_ne_top _)
    intro hz
    have hle := DMC.le_outputDist W p (x i) (y i)
    rw [hz, le_zero_iff, mul_eq_zero] at hle
    exact hle.elim (hp i) (hW i)
  have ha : ∀ i, (0 : ℝ) < (W.transition (x i) (y i)).toReal :=
    fun i ↦ ENNReal.toReal_pos (hW i) ((W.transition (x i)).apply_ne_top _)
  rw [DMC.outputPow_apply, DMC.power_transition_apply, ENNReal.toReal_prod, ENNReal.toReal_prod,
    ← Finset.prod_div_distrib, logb_prod_of_pos _ _ fun i _ ↦ div_pos (ha i) (hc i),
    DMC.infoDensityPow]
  rfl

/-- The decoder's mass-form failure event has joint probability at most the spectrum tail. -/
theorem sum_ite_le_spectrumTail (W : DMC X Y) (p : PMF X) (n : ℕ) (τ : ℝ) :
    ∑ z : (Fin n → X) × (Fin n → Y),
      (if ((W.power n).transition z.1 z.2).toReal
            ≤ (2 : ℝ) ^ τ * ((W.outputPow p n) z.2).toReal
        then (W.jointPow p n z).toReal else 0)
      ≤ W.spectrumTail p n τ := by
  classical
  rw [DMC.spectrumTail]
  refine Finset.sum_le_sum fun z _ ↦ ?_
  obtain ⟨x, y⟩ := z
  by_cases hz : W.jointPow p n (x, y) = 0
  · simp [hz]
  · have hWpos : (0 : ℝ) < ((W.power n).transition x y).toReal := by
      refine ENNReal.toReal_pos ?_ (((W.power n).transition x).apply_ne_top _)
      intro h0
      exact hz (by rw [DMC.jointPow, DMC.joint_apply, h0, mul_zero])
    have hout : (0 : ℝ) < ((W.outputPow p n) y).toReal := by
      refine ENNReal.toReal_pos ?_ ((W.outputPow p n).apply_ne_top _)
      intro h0
      apply hz
      rw [DMC.jointPow, DMC.joint_apply]
      rw [DMC.outputPow, PMF.bind_apply, tsum_fintype] at h0
      have := Finset.sum_eq_zero_iff.1 h0 x (Finset.mem_univ x)
      exact this
    dsimp only
    split
    · next hle =>
      have hi : W.infoDensityPow p n x y ≤ τ := by
        rw [infoDensityPow_eq_logb W p n hz]
        have hdiv : ((W.power n).transition x y).toReal / ((W.outputPow p n) y).toReal
            ≤ (2 : ℝ) ^ τ := by
          rw [div_le_iff₀ hout]; linarith
        calc Real.logb 2 (((W.power n).transition x y).toReal / ((W.outputPow p n) y).toReal)
            ≤ Real.logb 2 ((2 : ℝ) ^ τ) :=
              Real.logb_le_logb_of_le (by norm_num) (div_pos hWpos hout) hdiv
          _ = τ := Real.logb_rpow (by norm_num) (by norm_num)
      rw [if_pos hi]
    · split
      · exact ENNReal.toReal_nonneg
      · exact le_rfl

/-- The codeword indices whose likelihood ratio passes the threshold `2 ^ τ`. -/
noncomputable def passSet (W : DMC X Y) (p : PMF X) {n M : ℕ} (cb : Fin M → Fin n → X) (τ : ℝ)
    (y : Fin n → Y) : Finset (Fin M) :=
  Finset.univ.filter fun m ↦
    (2 : ℝ) ^ τ * ((W.outputPow p n) y).toReal < ((W.power n).transition (cb m) y).toReal

/-- Threshold decoding: return the least index that passes, and message `0` if none does.
Both the tie-break and the failure output are arbitrary; neither affects the error bound. -/
noncomputable def thresholdDecode (W : DMC X Y) (p : PMF X) {n M : ℕ} (hM : 0 < M)
    (cb : Fin M → Fin n → X) (τ : ℝ) (y : Fin n → Y) : Fin M :=
  if h : (passSet W p cb τ y).Nonempty then (passSet W p cb τ y).min' h else ⟨0, hM⟩

/-- The block code obtained from a codebook by threshold decoding. -/
noncomputable def randomCode (W : DMC X Y) (p : PMF X) {n M : ℕ} (hM : 0 < M)
    (cb : Fin M → Fin n → X) (τ : ℝ) : BlockCode X Y n where
  card := M
  card_pos := hM
  encode := cb
  decode := thresholdDecode W p hM cb τ

@[simp]
theorem randomCode_card (W : DMC X Y) (p : PMF X) {n M : ℕ} (hM : 0 < M)
    (cb : Fin M → Fin n → X) (τ : ℝ) : (randomCode W p hM cb τ).card = M := rfl

@[simp]
theorem randomCode_encode (W : DMC X Y) (p : PMF X) {n M : ℕ} (hM : 0 < M)
    (cb : Fin M → Fin n → X) (τ : ℝ) : (randomCode W p hM cb τ).encode = cb := rfl

@[simp]
theorem randomCode_decode (W : DMC X Y) (p : PMF X) {n M : ℕ} (hM : 0 < M)
    (cb : Fin M → Fin n → X) (τ : ℝ) :
    (randomCode W p hM cb τ).decode = thresholdDecode W p hM cb τ := rfl

/-- **Union bound**, per message: a decoding error means either the true codeword failed the
threshold, or some other codeword passed it. -/
theorem condError_randomCode_le (W : DMC X Y) (p : PMF X) {n M : ℕ} (hM : 0 < M)
    (cb : Fin M → Fin n → X) (τ : ℝ) (m : Fin M) :
    (randomCode W p hM cb τ).condError W m
      ≤ (∑ y : Fin n → Y, if m ∈ passSet W p cb τ y then 0
          else ((W.power n).transition (cb m) y).toReal)
        + ∑ m' ∈ Finset.univ.erase m, ∑ y : Fin n → Y,
            (if m' ∈ passSet W p cb τ y then
              ((W.power n).transition (cb m) y).toReal else 0) := by
  classical
  rw [BlockCode.condError, Finset.sum_comm, ← Finset.sum_add_distrib]
  simp only [randomCode_encode, randomCode_decode]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  have hA : (0 : ℝ) ≤ ((W.power n).transition (cb m) y).toReal := ENNReal.toReal_nonneg
  have hrest : (0 : ℝ) ≤ ∑ m' ∈ Finset.univ.erase m,
      (if m' ∈ passSet W p cb τ y then ((W.power n).transition (cb m) y).toReal else 0) :=
    Finset.sum_nonneg fun _ _ ↦ by split <;> [exact hA; exact le_rfl]
  split_ifs with hdec hmem hmem
  · linarith
  · linarith
  · rw [zero_add]
    have hne : (passSet W p cb τ y).Nonempty := ⟨m, hmem⟩
    have hval : thresholdDecode W p hM cb τ y = (passSet W p cb τ y).min' hne := by
      rw [thresholdDecode, dif_pos hne]
    have hmin : (passSet W p cb τ y).min' hne ∈ passSet W p cb τ y := Finset.min'_mem _ _
    have hnem : (passSet W p cb τ y).min' hne ≠ m := hval ▸ hdec
    calc ((W.power n).transition (cb m) y).toReal
        = (if (passSet W p cb τ y).min' hne ∈ passSet W p cb τ y then
            ((W.power n).transition (cb m) y).toReal else 0) := by rw [if_pos hmin]
      _ ≤ ∑ m' ∈ Finset.univ.erase m,
            (if m' ∈ passSet W p cb τ y then
              ((W.power n).transition (cb m) y).toReal else 0) :=
          Finset.single_le_sum
            (f := fun m' ↦ if m' ∈ passSet W p cb τ y then
              ((W.power n).transition (cb m) y).toReal else 0)
            (fun i _ ↦ by split <;> [exact hA; exact le_rfl])
            (Finset.mem_erase.2 ⟨hnem, Finset.mem_univ _⟩)
  · linarith

theorem ens_toReal {Z : Type*} [Fintype Z] (q : PMF Z) (M : ℕ) (cb : Fin M → Z) :
    ((PMF.pi fun _ : Fin M ↦ q) cb).toReal = ∏ k, (q (cb k)).toReal := by
  rw [PMF.pi_apply, ENNReal.toReal_prod]

theorem mem_passSet_iff (W : DMC X Y) (p : PMF X) {n M : ℕ} (cb : Fin M → Fin n → X) (τ : ℝ)
    (y : Fin n → Y) (m : Fin M) : m ∈ passSet W p cb τ y ↔
      (2 : ℝ) ^ τ * ((W.outputPow p n) y).toReal < ((W.power n).transition (cb m) y).toReal := by
  rw [passSet, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ m, h⟩⟩

/-- Ensemble average of the "true codeword failed the threshold" term. -/
theorem ens_term_one_le (W : DMC X Y) (p : PMF X) (n : ℕ) {M : ℕ} (τ : ℝ) (m : Fin M) :
    ∑ cb : Fin M → Fin n → X,
        ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
        * (∑ y : Fin n → Y, if m ∈ passSet W p cb τ y then 0
            else ((W.power n).transition (cb m) y).toReal)
      ≤ W.spectrumTail p n τ := by
  classical
  simp only [mem_passSet_iff]
  have hq : ∀ _k : Fin M, ∑ x : Fin n → X, ((PMF.pi fun _ : Fin n ↦ p) x).toReal = 1 :=
    fun _ ↦ sum_toReal_eq_one _
  have hstep : ∀ cb : Fin M → Fin n → X,
      ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
      = ∏ k, ((PMF.pi fun _ : Fin n ↦ p) (cb k)).toReal := fun cb ↦ ens_toReal _ _ _
  rw [Finset.sum_congr rfl fun cb _ ↦ by rw [hstep cb],
    sum_prod_mul (fun (_ : Fin M) (x : Fin n → X) ↦ ((PMF.pi fun _ : Fin n ↦ p) x).toReal) hq m
      fun x ↦ ∑ y : Fin n → Y, if (2 : ℝ) ^ τ * ((W.outputPow p n) y).toReal
        < ((W.power n).transition x y).toReal then 0
        else ((W.power n).transition x y).toReal]
  · refine le_trans (le_of_eq ?_) (sum_ite_le_spectrumTail W p n τ)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [W.jointPow_toReal p n (x, y)]
    dsimp only
    split_ifs with h1 h2 h2
    · exact absurd h1 (not_lt.2 h2)
    · ring
    · ring
    · exact absurd (not_lt.1 h1) h2

/-- Ensemble average of a "wrong codeword passed the threshold" term. -/
theorem ens_term_two_le (W : DMC X Y) (p : PMF X) (n : ℕ) {M : ℕ} (τ : ℝ) {m m' : Fin M}
    (hne : m' ≠ m) :
    ∑ cb : Fin M → Fin n → X,
        ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
        * (∑ y : Fin n → Y, if m' ∈ passSet W p cb τ y then
            ((W.power n).transition (cb m) y).toReal else 0)
      ≤ (2 : ℝ) ^ (-τ) := by
  classical
  have hq : ∀ _k : Fin M, ∑ x : Fin n → X, ((PMF.pi fun _ : Fin n ↦ p) x).toReal = 1 :=
    fun _ ↦ sum_toReal_eq_one _
  have hout : ∀ y : Fin n → Y, ∑ x : Fin n → X,
      ((PMF.pi fun _ : Fin n ↦ p) x).toReal * ((W.power n).transition x y).toReal
      = ((W.outputPow p n) y).toReal := by
    intro y
    rw [DMC.outputPow, PMF.bind_apply, tsum_fintype,
      ENNReal.toReal_sum fun x _ ↦ ENNReal.mul_ne_top ((PMF.pi _).apply_ne_top x)
        (((W.power n).transition x).apply_ne_top y)]
    exact (Finset.sum_congr rfl fun x _ ↦ ENNReal.toReal_mul).symm
  have hswap : ∀ cb : Fin M → Fin n → X,
      ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
        * (∑ y : Fin n → Y, if m' ∈ passSet W p cb τ y then
            ((W.power n).transition (cb m) y).toReal else 0)
      = ∑ y : Fin n → Y, (∏ k, ((PMF.pi fun _ : Fin n ↦ p) (cb k)).toReal)
          * ((if (2 : ℝ) ^ τ * ((W.outputPow p n) y).toReal
                < ((W.power n).transition (cb m') y).toReal then (1 : ℝ) else 0)
            * ((W.power n).transition (cb m) y).toReal) := by
    intro cb
    rw [ens_toReal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    simp only [mem_passSet_iff]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun cb _ ↦ hswap cb, Finset.sum_comm]
  have hinner : ∀ y : Fin n → Y,
      ∑ cb : Fin M → Fin n → X, (∏ k, ((PMF.pi fun _ : Fin n ↦ p) (cb k)).toReal)
        * ((if (2 : ℝ) ^ τ * ((W.outputPow p n) y).toReal
              < ((W.power n).transition (cb m') y).toReal then (1 : ℝ) else 0)
          * ((W.power n).transition (cb m) y).toReal)
      = (∑ x' : Fin n → X, ((PMF.pi fun _ : Fin n ↦ p) x').toReal
          * (if (2 : ℝ) ^ τ * ((W.outputPow p n) y).toReal
              < ((W.power n).transition x' y).toReal then (1 : ℝ) else 0))
        * ((W.outputPow p n) y).toReal := by
    intro y
    rw [sum_prod_mul_two (fun (_ : Fin M) (x : Fin n → X) ↦
        ((PMF.pi fun _ : Fin n ↦ p) x).toReal) hq hne
      (fun x' ↦ if (2 : ℝ) ^ τ * ((W.outputPow p n) y).toReal
        < ((W.power n).transition x' y).toReal then (1 : ℝ) else 0)
      fun x ↦ ((W.power n).transition x y).toReal, hout y]
  rw [Finset.sum_congr rfl fun y _ ↦ hinner y]
  refine le_trans (le_of_eq ?_) (sum_ite_lt_le_rpow_neg W p n τ)
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  split_ifs <;> ring

/-- **The random-coding bound.**  For any threshold `τ` there is a code with `M` messages whose
average error is at most the information-spectrum tail plus the union-bound term.

The codebook is drawn from the i.i.d. ensemble and decoded by thresholding the likelihood ratio.
A decoding error means either the true codeword failed the threshold — bounded by
`sum_ite_le_spectrumTail` — or some other codeword passed it, bounded by
`sum_ite_lt_le_rpow_neg` once the two codewords decouple.  A single good codebook is then
extracted with `exists_le_of_sum_toReal_mul_le`.

**No usable encoder comes out of this.**  The last step exhibits a codebook at least as good as
the ensemble average; it gives no way to find one (D-12). -/
theorem exists_blockCode_avgError_le (W : DMC X Y) (p : PMF X) (n : ℕ) {M : ℕ} (hM : 0 < M)
    (τ : ℝ) : ∃ c : BlockCode X Y n, c.card = M ∧
      c.avgError W ≤ W.spectrumTail p n τ + M * (2 : ℝ) ^ (-τ) := by
  classical
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hτ : (0 : ℝ) < (2 : ℝ) ^ (-τ) := Real.rpow_pos_of_pos (by norm_num) _
  have hper : ∀ m : Fin M,
      ∑ cb : Fin M → Fin n → X,
          ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
          * (randomCode W p hM cb τ).condError W m
        ≤ W.spectrumTail p n τ + (M : ℝ) * (2 : ℝ) ^ (-τ) := by
    intro m
    calc ∑ cb : Fin M → Fin n → X,
            ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
            * (randomCode W p hM cb τ).condError W m
        ≤ ∑ cb : Fin M → Fin n → X,
            ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
            * ((∑ y : Fin n → Y, if m ∈ passSet W p cb τ y then 0
                  else ((W.power n).transition (cb m) y).toReal)
              + ∑ m' ∈ Finset.univ.erase m, ∑ y : Fin n → Y,
                  (if m' ∈ passSet W p cb τ y then
                    ((W.power n).transition (cb m) y).toReal else 0)) :=
          Finset.sum_le_sum fun cb _ ↦
            mul_le_mul_of_nonneg_left (condError_randomCode_le W p hM cb τ m)
              ENNReal.toReal_nonneg
      _ = (∑ cb : Fin M → Fin n → X,
              ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
              * ∑ y : Fin n → Y, if m ∈ passSet W p cb τ y then 0
                  else ((W.power n).transition (cb m) y).toReal)
            + ∑ m' ∈ Finset.univ.erase m, ∑ cb : Fin M → Fin n → X,
                ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
                * ∑ y : Fin n → Y, (if m' ∈ passSet W p cb τ y then
                    ((W.power n).transition (cb m) y).toReal else 0) := by
          have hd : ∀ cb : Fin M → Fin n → X,
              ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
              * ((∑ y : Fin n → Y, if m ∈ passSet W p cb τ y then 0
                    else ((W.power n).transition (cb m) y).toReal)
                + ∑ m' ∈ Finset.univ.erase m, ∑ y : Fin n → Y,
                    (if m' ∈ passSet W p cb τ y then
                      ((W.power n).transition (cb m) y).toReal else 0))
              = ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
                  * (∑ y : Fin n → Y, if m ∈ passSet W p cb τ y then 0
                      else ((W.power n).transition (cb m) y).toReal)
                + ∑ m' ∈ Finset.univ.erase m,
                    ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
                    * ∑ y : Fin n → Y, (if m' ∈ passSet W p cb τ y then
                        ((W.power n).transition (cb m) y).toReal else 0) := by
            intro cb
            rw [mul_add]
            congr 1
            exact Finset.mul_sum _ _ _
          rw [Finset.sum_congr rfl fun cb _ ↦ hd cb, Finset.sum_add_distrib]
          congr 1
          exact Finset.sum_comm
      _ ≤ W.spectrumTail p n τ + (M : ℝ) * (2 : ℝ) ^ (-τ) := by
          refine add_le_add (ens_term_one_le W p n τ m) ?_
          calc ∑ m' ∈ Finset.univ.erase m, ∑ cb : Fin M → Fin n → X,
                  ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
                  * ∑ y : Fin n → Y, (if m' ∈ passSet W p cb τ y then
                      ((W.power n).transition (cb m) y).toReal else 0)
              ≤ ∑ _m' ∈ Finset.univ.erase m, (2 : ℝ) ^ (-τ) :=
                Finset.sum_le_sum fun m' hm' ↦
                  ens_term_two_le W p n τ (Finset.ne_of_mem_erase hm')
            _ = ((M : ℝ) - 1) * (2 : ℝ) ^ (-τ) := by
                rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ m),
                  Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                congr 1
                have : (1 : ℕ) ≤ M := hM
                push_cast [Nat.cast_sub this]
                ring
            _ ≤ (M : ℝ) * (2 : ℝ) ^ (-τ) := by nlinarith
  have havg : ∑ cb : Fin M → Fin n → X,
      ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
      * (randomCode W p hM cb τ).avgError W
      ≤ W.spectrumTail p n τ + (M : ℝ) * (2 : ℝ) ^ (-τ) := by
    have hrw : ∀ cb : Fin M → Fin n → X,
        ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
        * (randomCode W p hM cb τ).avgError W
        = (M : ℝ)⁻¹ * ∑ m : Fin M,
            ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
            * (randomCode W p hM cb τ).condError W m := by
      intro cb
      rw [BlockCode.avgError, mul_left_comm, Finset.mul_sum]
      rfl
    rw [Finset.sum_congr rfl fun cb _ ↦ hrw cb, ← Finset.mul_sum, Finset.sum_comm]
    calc (M : ℝ)⁻¹ * ∑ m : Fin M, ∑ cb : Fin M → Fin n → X,
            ((PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p) cb).toReal
            * (randomCode W p hM cb τ).condError W m
        ≤ (M : ℝ)⁻¹ * ∑ _m : Fin M, (W.spectrumTail p n τ + (M : ℝ) * (2 : ℝ) ^ (-τ)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ ↦ hper m) (by positivity)
      _ = W.spectrumTail p n τ + (M : ℝ) * (2 : ℝ) ^ (-τ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hMR), one_mul]
  obtain ⟨cb, _, hcb⟩ := exists_le_of_sum_toReal_mul_le
    (PMF.pi fun _ : Fin M ↦ PMF.pi fun _ : Fin n ↦ p)
    (fun cb ↦ (randomCode W p hM cb τ).avgError W) havg
  exact ⟨randomCode W p hM cb τ, rfl, hcb⟩

/-- **The weak law for the information spectrum.**  The normalised `n`-letter information
density concentrates at the mutual information, so the probability that it falls short of
`I - δ` vanishes. -/
theorem tendsto_spectrumTail (W : DMC X Y) (p : PMF X) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ W.spectrumTail p n ((n : ℝ) * (W.mutualInfo p - δ))) atTop (𝓝 0) := by
  classical
  set σ2 : ℝ := ∑ a : X × Y, ((W.joint p) a).toReal
    * (W.infoDensity p a.1 a.2 - W.mutualInfo p) ^ 2 with hσ2
  have hlim : Tendsto (fun n : ℕ ↦ σ2 / ((n : ℝ) * δ ^ 2)) atTop (𝓝 0) := by
    have heq : ∀ n : ℕ, σ2 / ((n : ℝ) * δ ^ 2) = (σ2 / δ ^ 2) * (1 / (n : ℝ)) := by
      intro n
      rw [mul_comm ((n : ℝ)) (δ ^ 2), ← div_div, div_eq_mul_one_div]
    simp only [heq]
    have hc : Tendsto (fun _ : ℕ ↦ σ2 / δ ^ 2) atTop (𝓝 (σ2 / δ ^ 2)) := tendsto_const_nhds
    simpa using hc.mul tendsto_one_div_atTop_nhds_zero_nat
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards with n
    rw [spectrumTail_eq]
    refine Finset.sum_nonneg fun w _ ↦ ?_
    split
    · exact Finset.prod_nonneg fun i _ ↦ ENNReal.toReal_nonneg
    · exact le_rfl
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact spectrumTail_le W p hδ hn

/-- `2 ^ (-n a) → 0` for `a > 0`. -/
theorem tendsto_rpow_neg_mul_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ (-((n : ℝ) * a))) atTop (𝓝 0) := by
  have hbase : (0 : ℝ) < (2 : ℝ) ^ (-a) := Real.rpow_pos_of_pos (by norm_num) _
  have hlt : (2 : ℝ) ^ (-a) < 1 := by
    rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by simp]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hcongr : ∀ n : ℕ, (2 : ℝ) ^ (-((n : ℝ) * a)) = ((2 : ℝ) ^ (-a)) ^ n := by
    intro n
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-a)) n, ← Real.rpow_mul (by norm_num)]
    ring_nf
  simpa [hcongr] using tendsto_pow_atTop_nhds_zero_of_lt_one hbase.le hlt

end FiniteDMC
