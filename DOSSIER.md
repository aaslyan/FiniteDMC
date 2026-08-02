# Fact dossier — the coding theorem for finite discrete memoryless channels in Lean 4

Collected 2026-08-01 against repository HEAD `80545d7` (branch `main`).
This document is **not** a paper. It is the frozen evidence base a paper is to
be written from. No prose, no argument, no promotion of proposals into results.

**Evidence tags.** Every statement carries exactly one.

| Tag | Meaning |
|---|---|
| `[VERIFIED-LEAN]` | Read from, or executed against, the Lean sources in this repository at `80545d7`. |
| `[VERIFIED-BUILD]` | Produced by running `lake build` or `lake env lean` at `80545d7` during this pass. |
| `[MEASURED]` | Objectively measured on the machine described in Part 7. |
| `[ENGINEERING]` | An implementation design decision, as recorded in the sources or reconstructible from them. |
| `[OPEN]` | Unresolved; needs a decision or evidence before use. |
| `[CORRECTED]` | A claim that was wrong in the repository's own prose and was fixed during this pass. |

**Verification environment for all `[MEASURED]` and `[VERIFIED-BUILD]` items.**
Apple M5, 10 cores, 32 GB RAM, macOS (Darwin 25.5.0); Lean
`leanprover/lean4:v4.32.2`; Mathlib `v4.32.2` at revision
`905b95818eb32af7874a58b427f50c1711a5e96c`; Mathlib oleans supplied by
`lake exe cache get`.

**Scope note.** This repository is further along than a first dossier pass
normally assumes: both top-level theorems are *proved*, not merely stated. The
dossier's job here is to verify and record that precisely, and to record what
the result does **not** say with the same care.

---

## Part 1 — What is proved

### 1.1 The two top-level statements, exactly as formalized

`[VERIFIED-LEAN]` `FiniteDMC/Achievability.lean:125`:

```lean
theorem coding_achievability [Nonempty X] (W : DMC X Y) {ε : ℝ}
    (hR : R < W.capacity) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ c : BlockCode X Y n, R ≤ c.rate ∧ c.avgError W ≤ ε
```

`[VERIFIED-LEAN]` `FiniteDMC/Converse.lean:335`:

```lean
theorem weak_converse (W : DMC X Y) {R : ℝ} (codes : ∀ n, BlockCode X Y n)
    (hrate : ∀ n, R ≤ (codes n).rate)
    (herr : Tendsto (fun n ↦ (codes n).avgError W) atTop (𝓝 0)) :
    R ≤ W.capacity
```

`[VERIFIED-LEAN]` `FiniteDMC/Converse.lean:358`:

```lean
theorem weak_converse_limsup (W : DMC X Y) (codes : ∀ n, BlockCode X Y n)
    (hbdd : BddAbove (Set.range fun n ↦ (codes n).rate))
    (herr : Tendsto (fun n ↦ (codes n).avgError W) atTop (𝓝 0)) :
    limsup (fun n ↦ (codes n).rate) atTop ≤ W.capacity
```

`[VERIFIED-BUILD]` Elaborated types, printed by `#check` against the built
environment:

```
@coding_achievability : ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X]
  [inst_1 : Fintype Y] {R : ℝ} [Nonempty X] (W : DMC X Y) {ε : ℝ},
  R < W.capacity → 0 < ε →
  ∀ᶠ (n : ℕ) in Filter.atTop, ∃ c, R ≤ c.rate ∧ c.avgError W ≤ ε

@weak_converse : ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X]
  [inst_1 : Fintype Y] (W : DMC X Y) {R : ℝ} (codes : (n : ℕ) → BlockCode X Y n),
  (∀ (n : ℕ), R ≤ (codes n).rate) →
  Filter.Tendsto (fun n => (codes n).avgError W) Filter.atTop (nhds 0) →
  R ≤ W.capacity

@weak_converse_limsup : ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X]
  [inst_1 : Fintype Y] (W : DMC X Y) (codes : (n : ℕ) → BlockCode X Y n),
  BddAbove (Set.range fun n => (codes n).rate) →
  Filter.Tendsto (fun n => (codes n).avgError W) Filter.atTop (nhds 0) →
  Filter.limsup (fun n => (codes n).rate) Filter.atTop ≤ W.capacity
```

### 1.2 Axiom footprint, re-verified fresh

`[VERIFIED-BUILD]` `#print axioms` executed during this pass against the built
environment. **Not** copied from `README.md` or `GOAL.md`.

```
'FiniteDMC.coding_achievability' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteDMC.weak_converse'        depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteDMC.weak_converse_limsup' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`[VERIFIED-BUILD]` The same command run on all twelve former obligations
(Part 3) returns the identical three-axiom list in every case. `sorryAx` appears
nowhere.

`[VERIFIED-BUILD]` `lake build` completes with **0 warnings** and no
`declaration uses 'sorry'`.

`[VERIFIED-LEAN]` `grep` for a proof-level `sorry` across `FiniteDMC/*.lean`
returns 0 matches.

`[ENGINEERING]` The three axioms are the standard classical base every Mathlib
theorem uses. The development introduces no axiom of its own and imports no
result from the literature unproved.

### 1.3 Supporting definitions

`[VERIFIED-LEAN]` `FiniteDMC/Channel.lean`:

```lean
structure DMC (X Y : Type*) [Fintype X] [Fintype Y] where
  transition : X → PMF Y
```

`[VERIFIED-LEAN]` `FiniteDMC/Code.lean`:

```lean
structure BlockCode (X Y : Type*) [Fintype X] [Fintype Y] (n : ℕ) where
  card     : ℕ
  card_pos : 0 < card
  encode   : Fin card → Fin n → X
  decode   : (Fin n → Y) → Fin card
```

`[VERIFIED-LEAN]` `FiniteDMC/Entropy.lean:188,193,198`:

```lean
noncomputable def entropy [Fintype α] (p : PMF α) : ℝ :=
  -∑ a : α, (p a).toReal * Real.logb 2 (p a).toReal

noncomputable def condEntropy [Fintype α] [Fintype β] (μ : PMF (α × β)) : ℝ :=
  entropy μ - entropy (μ.map Prod.snd)

noncomputable def mutualInfo [Fintype α] [Fintype β] (μ : PMF (α × β)) : ℝ :=
  entropy (μ.map Prod.fst) + entropy (μ.map Prod.snd) - entropy μ
```

`[VERIFIED-LEAN]` Every definition in the development is concrete. No `sorry`
ever stood for a deferred *definition*, so no definitional choice was hidden
behind an unproved obligation.

`[VERIFIED-LEAN]` Mathlib at this revision has no Shannon entropy or mutual
information for distributions on a `Fintype`. It supplies `Real.negMulLog`, a
binary entropy function, and a measure-theoretic Kullback–Leibler divergence;
the entropy layer here is built rather than imported.

---

## Part 2 — Convention decisions D-1 … D-12

### 2.1 Status legend

`[ENGINEERING]` The repository's own framing, retained here: these are **draft**
choices recorded for an information-theory collaborator to accept, amend, or
reject.

**No decision below has been reviewed or signed off.** Two distinct properties
are therefore tracked separately, and the second must not be read as the first:

| Column | Meaning |
|---|---|
| **Review status** | Whether a human with domain authority has confirmed the choice. |
| **Load-bearing** | Whether the completed proof now depends on it, so that revising it costs work. |

`[OPEN]` A convention becoming load-bearing is **not** evidence that it is
correct. It is evidence that changing it is now expensive. Every row below is
`[OPEN]` on review status.

### 2.2 The table, verbatim from `GOAL.md`

| # | Decision | Review status | Load-bearing |
|---|---|---|---|
| **D-1** | Scope: average error, direct + weak converse only. | `[OPEN]` | Yes — fixes what the theorems say. |
| **D-2** | `[Fintype X] [Fintype Y]` are parameters of `DMC` itself; `[Nonempty X]` is added **only** to `coding_achievability`, where it is genuinely needed. | `[OPEN]` | Yes — appears in the top-level signature. |
| **D-3** | Blocks are **`Fin n → X`**, not `Vector X n`. | `[OPEN]` | Yes — pervasive. |
| **D-4** | Base 2 throughout (`Real.logb 2`); `0 * log 0 = 0` obtained from Lean's junk value `log 0 = 0`. | `[OPEN]` | Yes — see Part 4.3. |
| **D-5** | `mutualInfo` and `condEntropy` defined by **inclusion–exclusion** (`I = H(A)+H(B)−H(A,B)`), not as a relative entropy. | `[OPEN]` | Yes — the entropy toolkit and both converse and achievability rest on it. **Highest-leverage decision in the repository.** |
| **D-6** | One distribution type: `PMF` over a `Fintype`; reals via `ENNReal.toReal` at point of use. | `[OPEN]` | Yes — pervasive. |
| **D-7** | Capacity is `sSup`, never `max`. | `[OPEN]` | Yes — see Part 4.2. |
| **D-8** | Message set is `Fin c.card`; rate is `logb 2 card / n`; size comparison written one way everywhere as `(2 : ℝ) ^ ((n : ℝ) * R) ≤ (c.card : ℝ)`. | `[OPEN]` | Yes — no statement anywhere mentions a floor or ceiling. |
| **D-9** | `BlockCode X Y n` does **not** mention the channel. | `[OPEN]` | Yes — structural. |
| **D-10** | Weak converse stated primarily in **R-form**; the limsup form carries an explicit `BddAbove` hypothesis. | `[OPEN]` | Yes — see Part 4.1. **Soundness flag, not taste.** |
| **D-11** | Deterministic encoder and decoder; uniform messages; error probability as a `Finset` sum, not `PMF.toMeasure`. | `[OPEN]` | Yes — and it held to the end; see Part 6.3. |
| **D-12** | Achievability is pure existence. | `[OPEN]` | Yes — see Part 4.5. |

`[VERIFIED-LEAN]` Deviations from the illustrative signatures in the original
brief: **D-3**, **D-8**, **D-9**, with **D-10** a correction to a drafted
statement rather than a presentational change.

### 2.3 D-4, D-7 and D-10 all turn on Lean junk values

`[ENGINEERING]` Three separate conventions depend on what Lean returns for an
undefined case. They are not the same hazard and are separated in Part 4: D-4's
junk value is *wanted*, D-7's and D-10's are *hazards*, and a fourth instance
(Part 4.4) was an outright defect.

---

## Part 3 — Obligation ledger

### 3.1 How the list was produced

`[ENGINEERING]` The obligations were not planned in prose. The method was:
state the two top-level theorems, attempt to prove them, and push each piece of
mathematical content that could not be immediately discharged into a *named,
precisely typed* `sorry`'d lemma. The resulting set of `sorry`s **is** the
dependency graph, discovered by the attempt rather than guessed in advance.

`[VERIFIED-LEAN]` A consequence recorded here because it is checkable: because
every `sorry` carried an exact type, none could hide an imprecise premise — a
mis-stated obligation would not have typechecked where it was used.

### 3.2 The ledger — all discharged, confirmed against live source

`[VERIFIED-LEAN]` Locations and existence confirmed by direct source read at
`80545d7`, not from `HARD-PARTS.md`'s historical record.
`[VERIFIED-BUILD]` Axiom footprint of every row is
`[propext, Classical.choice, Quot.sound]`.

| id | name | location | what it says |
|---|---|---|---|
| **S1** | `power_sum_eq_one` | `Channel.lean:64` | The `n`-fold product channel's rows sum to 1. |
| **S2** | `bddAbove_range_mutualInfo` | `Channel.lean:196` | The set of achievable mutual informations is bounded above. **Consumed by D-7; see Part 4.2.** |
| **S3** | `BlockCode.avgError_le_one` | `Converse.lean:60` | Average error probability is at most 1. |
| **S4** | `BlockCode.entropy_messageDist` | `Converse.lean:87` | The uniform message law has entropy `log₂ |M|`. |
| **S5** | `BlockCode.msgOutJoint_map_fst` | `Converse.lean:98` | The message marginal of the joint law is uniform. |
| **S6** | `BlockCode.le_rate_of_rpow_le_card` | `Achievability.lean:43` | Enough messages implies enough rate. |
| **S7** | `BlockCode.fano_inequality` | `Converse.lean:120` | Fano's inequality for a block code: `H(M ∣ Yⁿ) ≤ 1 + Pe · log₂ |M|`. |
| **S8** | `BlockCode.mutualInfo_msgOutJoint_le` | `Converse.lean:248` | Data processing along `M → Xⁿ → Yⁿ`. |
| **S9** | `DMC.mutualInfo_power_le` | `Converse.lean:263` | Single-letterisation: `I(Xⁿ;Yⁿ) ≤ n · C`. |
| **S10** | `exists_blockCode_of_lt_mutualInfo` | `Achievability.lean:60` | Achievability at a fixed input law. Proved *from* S10a and S10b. |
| **S10a** | `exists_blockCode_avgError_le` | `RandomCoding.lean:626` | The random-coding bound. |
| **S10b** | `tendsto_spectrumTail` | `RandomCoding.lean:727` | The weak law for the information spectrum. |
| **S11** | `weak_converse_limsup` | `Converse.lean:358` | The limsup form of the converse. |

`[VERIFIED-LEAN]` `logb_card_le_capacity` (`Converse.lean:304`) is the assembled
one-shot Fano bound `log₂|M| ≤ n·C + 1 + Pe·log₂|M|`; it was never an
obligation, but is the hinge the converse turns on.

### 3.3 Categories that came out empty

`[VERIFIED-LEAN]` Classified using the original brief's own categories
(Definition, Lemma, Theorem, Construction, Algorithm, Measurement, External
fact), every obligation was a **Lemma** or a **Theorem**. Three categories were
empty from the start and stayed empty:

* **Definition** — none deferred, so no `sorry` hid a definitional choice.
* **Algorithm** — none, by design (D-12).
* **External fact** — nothing taken from the literature unproved.

### 3.4 Two findings from the discharge process

`[VERIFIED-LEAN]` **S8 is an equality, not an inequality.** A code's
message-to-output link is `DMC.joint` of an induced `codeChannel`, and change of
variables along the encoder identifies the two mutual informations exactly. The
proof is `le_of_eq`; the data-processing *inequality* is never needed.

`[VERIFIED-LEAN]` **Fano needs no case split on `|M| = 1`.** Gibbs' inequality
is stated for a *sub-probability weight* (`w ≥ 0`, `∑ w ≤ 1`) rather than a
`PMF` (`entropy_le_neg_sum_mul_logb`, `EntropyBounds.lean`). The reference
weight used in Fano has total mass 1 when `|M| ≥ 2` and 1/2 when `|M| = 1`, and
the inequality is indifferent, so the degenerate case absorbs itself.

---

## Part 4 — Hazards

The two flagged most prominently are 4.1 and 4.2. Both are subtle, both are
junk-value dependencies, and both would be invisible to a reader checking only
that the build is green.

### 4.1 `limsup` on `ℝ` is an `sInf` — the D-10 hazard

`[VERIFIED-LEAN]` `Filter.limsup u f` on `ℝ` is `sInf {a | ∀ᶠ n in f, u n ≤ a}`.
For a sequence unbounded above, that set is **empty**, and `Real.sInf_empty`
gives `0`.

`[VERIFIED-BUILD]` Demonstrated executably during this pass:

```lean
example : Filter.limsup (fun n : ℕ ↦ (n : ℝ)) Filter.atTop = 0 := by
  have hset : {a : ℝ | ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ≤ a} = ∅ := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
    obtain ⟨m, hm⟩ := exists_nat_gt a
    exact absurd (hN (max N m) (le_max_left _ _))
      (not_le.2 (lt_of_lt_of_le hm (by exact_mod_cast le_max_right N m)))
  rw [Filter.limsup_eq, hset, Real.sInf_empty]
```

`[ENGINEERING]` **Consequence.** The original brief drafted the weak converse in
`limsup` form with no boundedness hypothesis. As drafted, a code sequence with
*unbounded* rate and vanishing error would satisfy `limsup rate ≤ C` vacuously —
the statement would be strictly weaker than intended, in exactly the direction
that matters. The repository's response was to make the `R`-form primary
(`weak_converse`) and give the limsup form an explicit `BddAbove` hypothesis
(`weak_converse_limsup`, `Converse.lean:358`).

`[VERIFIED-LEAN]` This is the only place in the development where a *drafted
statement's meaning* was changed rather than its presentation.

### 4.2 `sSup` of an unbounded set is `0` — the D-7 / S2 dependency

`[VERIFIED-BUILD]` `Real.sSup_of_not_bddAbove : ¬BddAbove s → sSup s = 0`, and
`Real.sSup_empty : sSup ∅ = 0`.

`[VERIFIED-LEAN]` `DMC.capacity W := sSup (Set.range fun p : PMF X ↦ W.mutualInfo p)`
(`Channel.lean`).

`[ENGINEERING]` **Consequence.** If `bddAbove_range_mutualInfo` (S2) were false
or simply never proved, `capacity` would silently evaluate to the junk value `0`
rather than being undefined or erroring. The failure would be *directional* and
asymmetric:

* `coding_achievability` has hypothesis `R < capacity`. With `capacity = 0` this
  is nearly vacuous — the theorem would still typecheck and still be provable,
  while asserting almost nothing.
* `weak_converse` concludes `R ≤ capacity`. With `capacity = 0` this would be
  false for any real channel, so the failure would surface as an unprovable
  goal.

`[VERIFIED-LEAN]` S2 is therefore **not bureaucratic**. It is consumed
concretely: single-letterisation (S9) bounds a mutual information against the
supremum via `le_csSup`, which requires `BddAbove`. `[VERIFIED-LEAN]` S2 is
proved by `I ≤ H(Y) ≤ log₂|Y|` — through the output alphabet, not the input.

### 4.3 `Real.logb 2 0 = 0` — the D-4 junk value, wanted

`[VERIFIED-BUILD]` `Real.logb 2 0 = 0` by `simp`.

`[ENGINEERING]` This one is *load-bearing and desirable*: it delivers the
standard `0 · log 0 = 0` convention, making `entropy` total with no support
hypothesis and no case split anywhere. `[VERIFIED-LEAN]` But it arrives as a
junk value rather than as a stated convention, which is why it is guarded by a
closed check rather than assumed (Part 6.2).

### 4.4 The same junk value as an outright defect — and its quarantine

`[VERIFIED-LEAN]` `DMC.infoDensity W p x y := Real.logb 2 ((W.transition x y).toReal / ((p.bind W.transition) y).toReal)`
(`RandomCoding.lean`). Because `Real.logb` sends `0` to `0`, a pair with
`W(y ∣ x) = 0` and `P_Y(y) > 0` receives information density **`0`**, where
information theory requires **`−∞`**.

`[VERIFIED-BUILD]` Confirmed executably:

```lean
example (W : DMC Bool Bool) (p : PMF Bool) (x y : Bool)
    (h : W.transition x y = 0) : W.infoDensity p x y = 0 := by
  simp [DMC.infoDensity, h]
```

`[ENGINEERING]` **Where it is harmless.** Under the *joint* law, which puts no
mass on such pairs. Every use in the weak law is under the joint.

`[ENGINEERING]` **Where it bites.** The union-bound term of the random-coding
argument sums against a *product of marginals*, which does charge those pairs.
There the change-of-measure bound `P_Yⁿ(y) ≤ 2^(−τ) · Wⁿ(y ∣ x)` fails outright,
its right-hand side being zero.

`[VERIFIED-LEAN]` **The resolution was quarantine, not patch.** Three facts:

* `sum_ite_lt_le_rpow_neg` (`RandomCoding.lean`) states change of measure as a
  **mass inequality with no logarithm** — the event is
  `2 ^ τ * P_Yⁿ(y) < Wⁿ(y ∣ x)`.
* `infoDensityPow_eq_logb` (`RandomCoding.lean`) connects the log-sum form to
  the mass form **under the hypothesis `W.jointPow p n (x, y) ≠ 0`** — exactly
  the condition under which the two agree.
* `sum_ite_le_spectrumTail` (`RandomCoding.lean`) bounds the joint probability
  that the true codeword fails the mass test by `spectrumTail`.

`[ENGINEERING]` The defect cannot leak because the bridging lemma will not apply
where it would be wrong. `spectrumTail` keeps its log-sum phrasing, so the weak
law (S10b) needed no rework.

`[ENGINEERING]` This defect was introduced and caught within the same
development; it never reached a released state. It is recorded because a
"complete, green" build would have contained a false lemma had the
change-of-measure step not been written out explicitly.

### 4.5 Non-constructivity is real and localised — D-12

`[VERIFIED-LEAN]` `exists_le_of_sum_toReal_mul_le` (`RandomCoding.lean:74`):
`(∑ i, (μ i).toReal * f i ≤ b) → ∃ i, μ i ≠ 0 ∧ f i ≤ b`.

`[ENGINEERING]` This is the step that makes random coding non-constructive: it
exhibits a codebook at least as good as the ensemble average and yields no
procedure for finding one. It is isolated in a single named lemma rather than
buried in the argument, which is what makes the claim auditable.

`[VERIFIED-LEAN]` `thresholdDecode` (`RandomCoding.lean`) additionally makes two
arbitrary choices — least-index tie-break among codewords passing the threshold,
and message `0` when none passes. `[ENGINEERING]` Neither affects the error
bound; both are recorded because they are stipulations, not derivations.

---

## Part 5 — What is NOT built

`[CORRECTED]` `GOAL.md` §5 previously listed the pigeonhole step and the i.i.d.
ensemble as absent. Both exist. The section was rewritten during this pass; the
corrected content is recorded below. **This dossier does not carry the stale
list forward.**

### 5.1 Built, despite earlier prose to the contrary

`[VERIFIED-LEAN]` `exists_le_of_sum_toReal_mul_le` — `RandomCoding.lean:74`.
`[VERIFIED-LEAN]` `PMF.pi` — `RandomCoding.lean:53`, the product of a finite
family of `PMF`s, supplying both the i.i.d. input law and the codebook ensemble.
Mathlib has no such construction at this revision.

### 5.2 Genuinely absent

`[VERIFIED-LEAN]` **The joint-typicality set and its estimates.** Absent *by
choice of route, not by omission*: achievability was formalised along the
information-density threshold route, which needs one concentration estimate
rather than three and no typicality set at all. `grep` for `typical` across the
sources matches only prose in `RandomCoding.lean`'s module docstring explaining
the choice.

`[VERIFIED-LEAN]` **Attainment of capacity** (`∃ p, I(p ; W) = C`). Not present,
and deliberately not a prerequisite for stating capacity (D-7). Would require
compactness of the probability simplex and continuity of `mutualInfo`.

`[VERIFIED-LEAN]` **Continuity and concavity of `mutualInfo`.** Not present.

`[VERIFIED-LEAN]` **Identification of D-5's `mutualInfo` with the
Kullback–Leibler form.** Not present. This is the standing cost of D-5:
inclusion–exclusion was taken as the definition, so agreement with the relative-
entropy form is a lemma nobody has needed yet.

### 5.3 Out of scope by construction

`[VERIFIED-LEAN]` Recorded in `README.md` and the root module docstring, and
enforced by what the statements quantify over: maximal error probability,
the strong converse, expurgation, feedback, continuous or infinite alphabets,
Shannon–Hartley, zero-error capacity. `[ENGINEERING]` Nothing in the repository
is built toward any of these.

### 5.4 What the theorems do not say, even as proved

`[ENGINEERING]` Recorded because the gap between "the coding theorem is proved"
and what a reader may assume is wide:

* Average error over uniform messages, **not** maximal error.
* Weak converse: above capacity the error cannot vanish. It is **not** shown
  that error tends to 1 (that is the strong converse).
* Nothing is claimed at `R = C`; achievability is strict below, the converse
  strict above.
* Existence, not construction (Part 4.5).
* The definitions are stipulations. That they mean what an information theorist
  means is assumed, not proved, and is not the kind of thing a proof assistant
  can check. `[OPEN]` This remains the only layer where human review is the
  instrument, and no such review has occurred.

---

## Part 6 — Repository facts

### 6.1 Module inventory

`[VERIFIED-LEAN]` Nine modules; dependency order top to bottom.

| module | role |
|---|---|
| `FiniteDMC/Entropy.lean` | `entropy`, `condEntropy`, `mutualInfo`; `PMF` utilities on a `Fintype`. |
| `FiniteDMC/EntropyBounds.lean` | non-negativity, Gibbs, maximum entropy, subadditivity across coordinates. |
| `FiniteDMC/Channel.lean` | `DMC`, memoryless `n`-fold extension, joint law, capacity, the normal form `DMC.mutualInfo_eq`. |
| `FiniteDMC/Code.lean` | `BlockCode`, rate, conditional and average error, induced joint laws. |
| `FiniteDMC/RandomCoding.lean` | `PMF.pi`, information density, spectrum tail, threshold decoder, the random-coding bound. |
| `FiniteDMC/Achievability.lean` | the direct theorem. |
| `FiniteDMC/Converse.lean` | Fano, data processing, single-letterisation, the weak converse. |
| `FiniteDMC/Sanity.lean` | closed convention checks; nothing depends on it. |
| `FiniteDMC.lean` | root; imports all of the above. |

### 6.2 Convention checks that are closed proofs

`[VERIFIED-LEAN]` `FiniteDMC/Sanity.lean` contains four `example`s with real
proofs and no `sorry`. `[ENGINEERING]` They exist so the conventions a reader
would otherwise take on trust cannot be silently degenerate. `[VERIFIED-BUILD]`
They compile as part of `lake build`; being anonymous `example`s they cannot be
targeted by `#print axioms`.

| check | guards |
|---|---|
| `entropy (PMF.uniformOfFintype Bool) = 1` | entropy is in **bits** (D-4). |
| `entropy (PMF.pure a) = 0` | the `0 log 0 = 0` convention holds with no support hypothesis (D-4). |
| `(W.power n).transition x y = ∏ i, W.transition (x i) (y i)` by `rfl` | memorylessness is definitional, not an added axiom (D-3). |
| `(W.power 1).transition x y = W.transition (x 0) (y 0)` | the length-1 extension is faithful. |

### 6.3 D-11 held end to end

`[VERIFIED-LEAN]` `grep` for `toMeasure` across the sources returns exactly one
match, and it is prose: `Code.lean:35`, a module docstring recording that the
`Finset`-sum formulation "avoids dragging in `PMF.toMeasure`". There is no
*use*. `[ENGINEERING]` The decision to stay with `Finset` sums on finite types
and avoid measure theory was taken in the first session for convenience, before
it was known whether it would survive the concentration argument. It did: the
law of large numbers (S10b) is proved by a bespoke finite-alphabet Chebyshev
bound rather than by bridging to Mathlib's measure-theoretic strong law.

`[VERIFIED-LEAN]` `Real.log_le_sub_one_of_pos` is invoked exactly once, at
`EntropyBounds.lean:77`, inside Gibbs' inequality — from which the maximum-
entropy bound, subadditivity and Fano all follow. `[VERIFIED-LEAN]` `grep` for
`Jensen`, `ConvexOn`, `ConcaveOn` and `inner_le_weight` across the sources
returns one match, again prose: the `EntropyBounds.lean` module docstring
asserting the absence. No convexity lemma is applied anywhere.

### 6.4 A reusable abstraction

`[VERIFIED-LEAN]` `sum_prod_mul` (`Entropy.lean`) — summing a product weight
against a function of a single coordinate collapses to that coordinate's factor
— is stated over an arbitrary `CommSemiring`. `[ENGINEERING]` It therefore does
duty in three places that would otherwise need separate proofs: the real-valued
entropy computation, the `ℝ≥0∞` marginal computation, and the variance
calculation in S10b. Its two-coordinate companion `sum_prod_mul_two` follows
from `Fintype.prod_sum` and `Finset.prod_ite_eq'` with no erasing argument.

### 6.5 Build status and CI

`[VERIFIED-BUILD]` `lake build` succeeds; 2601 jobs; 0 warnings; 0 `sorry`.
`[VERIFIED-LEAN]` No lines exceed 100 characters (Mathlib's limit), measured by
character count, not bytes.

`[OPEN]` **There is no CI.** The `lean_action_ci.yml` workflow generated by
`lake init` was stripped from the repository history in order to push without
the GitHub `workflow` OAuth scope. `[ENGINEERING]` Consequence: the repository's
public claim of a `sorry`-free build has no mechanical backing for a visitor;
verification requires a local clone and build. Restoring it is a one-file commit
once the scope is granted, and needs no history rewrite.

---

## Part 7 — Measurements

`[MEASURED]` Machine and toolchain as given at the head of this document.

### 7.1 Source size

| file | lines |
|---|---|
| `FiniteDMC/RandomCoding.lean` | 762 |
| `FiniteDMC/Converse.lean` | 377 |
| `FiniteDMC/Channel.lean` | 286 |
| `FiniteDMC/Entropy.lean` | 211 |
| `FiniteDMC/EntropyBounds.lean` | 171 |
| `FiniteDMC/Achievability.lean` | 136 |
| `FiniteDMC/Code.lean` | 110 |
| `FiniteDMC/Sanity.lean` | 50 |
| `FiniteDMC.lean` | 24 |
| **total** | **2127** |

### 7.2 Declaration counts

`[MEASURED]` 77 theorems/lemmas; 25 definitions and structures; 4 `example`s.

### 7.3 Build time

`[MEASURED]` Clean rebuild of the FiniteDMC modules only (`rm -rf .lake/build`,
then `lake build`, with Mathlib oleans already present): **13 s**.
`[ENGINEERING]` This excludes Mathlib, which is supplied by `lake exe cache get`
and not rebuilt.

### 7.4 Repository history

`[MEASURED]` 13 commits on `main` at the time of collection.
`[VERIFIED-LEAN]` `.github/` is absent from every ref; it was removed from all
history by `git filter-branch` prior to the first push, with commit messages
preserved byte-for-byte and only hashes changed.

---

## Part 8 — Claims audit

### 8.1 Safe claims — fully supported by evidence in this dossier

`[VERIFIED-BUILD]` "Both directions of the coding theorem for finite discrete
memoryless channels are proved in Lean 4, with no `sorry`, depending only on
`propext`, `Classical.choice` and `Quot.sound`."

`[VERIFIED-LEAN]` "The development uses no measure theory; the law of large
numbers is proved by an elementary finite-alphabet Chebyshev bound."

`[VERIFIED-LEAN]` "Mathlib has no discrete Shannon entropy at this revision; the
entropy layer is built here, resting on `Real.log_le_sub_one_of_pos` alone."

`[VERIFIED-LEAN]` "Every obligation was a Lemma or a Theorem; none was a
deferred Definition, an Algorithm, or an external fact."

`[VERIFIED-LEAN]` "Achievability is an existence result; the non-constructive
step is isolated in `exists_le_of_sum_toReal_mul_le`."

### 8.2 Unsafe claims — currently wrong, or needing evidence not yet gathered

`[OPEN]` "The definitions are correct." Not established. Nobody with domain
authority has reviewed D-1 … D-12. The proof's completeness is evidence about
the *derivations*, not about whether `capacity`, `avgError`, `rate` and
`mutualInfo` mean what they should.

`[OPEN]` "This is a complete formalisation of Shannon's channel coding
theorem." Overclaims. Finite alphabets, average error, weak converse only; see
Part 5.3 and 5.4.

`[OPEN]` "The formalisation yields a code construction." False. See Part 4.5.

`[OPEN]` "The build is verified on every commit." False at present. See
Part 6.5.

`[OPEN]` "The obligation sizes recorded in `HARD-PARTS.md` are measurements."
They are estimates made before the work, retained as a record of estimate
against outcome. Only the ~200-line figure for S9 was checked after the fact,
via `git diff --numstat`.

`[OPEN]` No comparison against prior formalisations of Shannon theory (for
example in Coq/SSReflect's `infotheo`) has been carried out. Any novelty claim
requires that survey first.

---

## Part 9 — Corrections made during this pass

`[CORRECTED]` Four claims in the repository's own prose described real earlier
states that the surrounding text was never updated past. None indicated an
error in any proof. All four were fixed at `80545d7`.

| where | was | now |
|---|---|---|
| `Converse.lean` module docstring | "`DMC.mutualInfo_power_le` is the one remaining `sorry`" | the converse chain is complete and unconditional |
| `HARD-PARTS.md` header note | "S10 is now the only open obligation in the repository" | two-stage update recording that S10a and S10b are both discharged |
| `GOAL.md` §5 | listed the pigeonhole step and the i.i.d. ensemble as not built | separates what was built from what is genuinely absent, and records that the joint-typicality set is absent by choice of route |
| `GOAL.md` D-12, `Achievability.lean` | "its **intended** proof is random coding" | it is the proof |

`[ENGINEERING]` The third was not in the brief for this pass; it was found by
checking the brief's own premise against source. Had it been carried forward
unchecked, this dossier would have recorded two built components as absent.
