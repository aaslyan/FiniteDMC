/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import FiniteDMC.EntropyBounds

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

## Main statements

* `FiniteDMC.DMC.entropy_joint` : the chain rule `H(X, Y) = H(X) + ∑ₓ p x · H(W(· ∣ x))`.
* `FiniteDMC.DMC.mutualInfo_eq` : the normal form `I(p ; W) = H(Y) - ∑ₓ p x · H(W(· ∣ x))`, which
  is what makes the capacity bound and the data-processing step routine.
* `FiniteDMC.bddAbove_range_mutualInfo` : capacity is a supremum of a bounded set, so it is not
  the junk value `0`.

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
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun i _ ↦ sum_coe_eq_one (W.transition (x i))

/-- The `n`-fold memoryless extension `Wⁿ` of a DMC `W`: a DMC from length-`n` input blocks to
length-`n` output blocks whose transition law is the product of the per-symbol transition laws.

Memorylessness is built into the definition rather than being an extra hypothesis. -/
noncomputable def DMC.power (W : DMC X Y) (n : ℕ) : DMC (Fin n → X) (Fin n → Y) where
  transition x := PMF.ofFintype (fun y ↦ ∏ i, W.transition (x i) (y i)) (power_sum_eq_one W n x)

@[simp]
theorem DMC.power_transition_apply (W : DMC X Y) (n : ℕ) (x : Fin n → X) (y : Fin n → Y) :
    (W.power n).transition x y = ∏ i, W.transition (x i) (y i) := rfl

/-- The joint input-output mass function is normalised. -/
theorem joint_sum_eq_one (W : DMC X Y) (p : PMF X) :
    ∑ z : X × Y, p z.1 * W.transition z.1 z.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, sum_coe_eq_one, mul_one]
  exact sum_coe_eq_one p

/-- The joint input-output distribution on `X × Y` obtained by feeding the input law `p` into the
channel `W`.

Presented as an explicit mass function `p x * W (y ∣ x)` rather than as `p.bind`, so that
`DMC.joint_apply` holds by `rfl`; this matches `DMC.power` and keeps the entropy computations
below purely calculational. -/
noncomputable def DMC.joint (W : DMC X Y) (p : PMF X) : PMF (X × Y) :=
  PMF.ofFintype (fun z ↦ p z.1 * W.transition z.1 z.2) (joint_sum_eq_one W p)

@[simp]
theorem DMC.joint_apply (W : DMC X Y) (p : PMF X) (x : X) (y : Y) :
    W.joint p (x, y) = p x * W.transition x y := rfl

/-- The input marginal of the joint law is the input law. -/
@[simp]
theorem DMC.joint_map_fst (W : DMC X Y) (p : PMF X) :
    (W.joint p).map Prod.fst = p := by
  classical
  ext x
  rw [map_apply_fintype, Fintype.sum_prod_type]
  simp only [DMC.joint, PMF.ofFintype_apply]
  rw [Finset.sum_eq_single x]
  · simp [← Finset.mul_sum, sum_coe_eq_one]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- The output marginal of the joint law is the input law pushed through the channel. -/
@[simp]
theorem DMC.joint_map_snd (W : DMC X Y) (p : PMF X) :
    (W.joint p).map Prod.snd = p.bind W.transition := by
  classical
  ext y
  rw [map_apply_fintype, PMF.bind_apply, tsum_fintype, Fintype.sum_prod_type]
  simp only [DMC.joint, PMF.ofFintype_apply]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- The entropy of the joint law splits as input entropy plus average conditional entropy:
`H(X, Y) = H(X) + ∑ₓ p x · H(W(· ∣ x))`.

This is the chain rule for a channel joint, and it is the workhorse for everything below. -/
theorem DMC.entropy_joint (W : DMC X Y) (p : PMF X) :
    entropy (W.joint p) = entropy p + ∑ x, (p x).toReal * entropy (W.transition x) := by
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      (a * b) * Real.logb 2 (a * b) = (a * b) * Real.logb 2 a + (a * b) * Real.logb 2 b := by
    intro a b ha hb
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h]; simp
    rcases eq_or_lt_of_le hb with h' | h'
    · rw [← h']; simp
    · rw [Real.logb, Real.logb, Real.logb, Real.log_mul (ne_of_gt h) (ne_of_gt h')]
      ring
  have expand : ∀ x : X, ∑ y : Y, ((p x).toReal * (W.transition x y).toReal) *
        Real.logb 2 ((p x).toReal * (W.transition x y).toReal)
      = (p x).toReal * Real.logb 2 (p x).toReal - (p x).toReal * entropy (W.transition x) := by
    intro x
    have hsum : ∑ y : Y, (W.transition x y).toReal = 1 := sum_toReal_eq_one _
    have hent : ∑ y : Y, (W.transition x y).toReal * Real.logb 2 (W.transition x y).toReal
        = -entropy (W.transition x) := by
      rw [entropy, neg_neg]
    calc ∑ y : Y, ((p x).toReal * (W.transition x y).toReal) *
            Real.logb 2 ((p x).toReal * (W.transition x y).toReal)
        = ∑ y : Y, ((p x).toReal * Real.logb 2 (p x).toReal * (W.transition x y).toReal
            + (p x).toReal * ((W.transition x y).toReal
                * Real.logb 2 (W.transition x y).toReal)) := by
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          rw [key _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
          ring
      _ = (p x).toReal * Real.logb 2 (p x).toReal * (∑ y : Y, (W.transition x y).toReal)
            + (p x).toReal * (∑ y : Y, (W.transition x y).toReal
                * Real.logb 2 (W.transition x y).toReal) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = (p x).toReal * Real.logb 2 (p x).toReal
            - (p x).toReal * entropy (W.transition x) := by
          rw [hsum, hent]; ring
  rw [entropy, Fintype.sum_prod_type]
  simp only [DMC.joint_apply, ENNReal.toReal_mul]
  rw [Finset.sum_congr rfl fun x _ ↦ expand x, Finset.sum_sub_distrib, entropy]
  ring

/-- The mutual information `I(p ; W)` between the input and the output of `W` when the input is
distributed according to `p`, in bits. -/
noncomputable def DMC.mutualInfo (W : DMC X Y) (p : PMF X) : ℝ :=
  FiniteDMC.mutualInfo (W.joint p)

/-- The capacity `C = sup_p I(p ; W)` of a finite DMC, in bits per channel use.

Stated as a supremum: attainment is a separate theorem, not a prerequisite. -/
noncomputable def DMC.capacity (W : DMC X Y) : ℝ :=
  sSup (Set.range fun p : PMF X ↦ W.mutualInfo p)

/-- Mutual information across a channel in terms of output entropy minus average conditional
entropy: `I(p ; W) = H(Y) - ∑ₓ p x · H(W(· ∣ x))`. -/
theorem DMC.mutualInfo_eq (W : DMC X Y) (p : PMF X) :
    W.mutualInfo p
      = entropy (p.bind W.transition) - ∑ x, (p x).toReal * entropy (W.transition x) := by
  rw [DMC.mutualInfo, FiniteDMC.mutualInfo, W.joint_map_fst p, W.joint_map_snd p,
    W.entropy_joint p]
  ring

/-- The set of achievable mutual informations of a finite DMC is bounded above.

Needed for `sSup` to mean what it should: without it `DMC.capacity` would be the junk value `0`.
Mathematically `I(p ; W) ≤ log₂ (Fintype.card X)`, but any bound will do. -/
theorem bddAbove_range_mutualInfo (W : DMC X Y) :
    BddAbove (Set.range fun p : PMF X ↦ W.mutualInfo p) := by
  classical
  refine ⟨Real.logb 2 (Fintype.card Y), ?_⟩
  rintro _ ⟨p, rfl⟩
  haveI : Nonempty Y := nonempty_of_pmf (p.bind W.transition)
  change W.mutualInfo p ≤ _
  rw [W.mutualInfo_eq p]
  have h1 : entropy (p.bind W.transition) ≤ Real.logb 2 (Fintype.card Y) :=
    entropy_le_logb_card _
  have h2 : 0 ≤ ∑ x, (p x).toReal * entropy (W.transition x) :=
    Finset.sum_nonneg fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg (entropy_nonneg _)
  linarith

end FiniteDMC
