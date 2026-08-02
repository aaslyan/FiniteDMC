# S9 and S10 — the two obligations worth discussing before attempting

Companion to [`GOAL.md`](GOAL.md). These are the two `sorry`s that are not
routine. Everything asserted here about Mathlib was checked against
Mathlib v4.32.2 in this repository, not recalled.

**Summary of the difference between them.** S9 is *large but standard*: every
step is a textbook lemma, and the work is volume, not invention. S10 is
*genuinely a design decision*: there are several inequivalent proofs of
achievability, they have very different formalization costs, and the
conventional textbook one is probably the worst choice here.

---

## S9 — single-letterisation

```lean
theorem DMC.mutualInfo_power_le (W : DMC X Y) (n : ℕ) (q : PMF (Fin n → X)) :
    (W.power n).mutualInfo q ≤ n * W.capacity
```

*`n` uses of a memoryless channel carry at most `n · C` bits, whatever the joint
law of the input block — including a law with dependence across coordinates.*

### The textbook argument

With `Xⁿ ~ q` and `Yⁿ ~ Wⁿ(·|Xⁿ)`:

```
I(Xⁿ;Yⁿ)  =  H(Yⁿ) − H(Yⁿ|Xⁿ)
          =  H(Yⁿ) − Σᵢ H(Yᵢ|Xᵢ)        (memorylessness)
          ≤  Σᵢ H(Yᵢ) − Σᵢ H(Yᵢ|Xᵢ)     (subadditivity)
          =  Σᵢ I(Xᵢ;Yᵢ)
          ≤  n · C                       (each Xᵢ is *some* input law)
```

Note where the hypotheses actually bite. Memorylessness is used exactly once,
in the second line, and it is available *definitionally* here: `DMC.power`'s
transition law is literally `∏ i, W (yᵢ|xᵢ)`, so "conditioned on `Xⁿ = x`, the
`Yᵢ` are independent" is not a fact to be established — it is the definition.
The only genuine inequality is subadditivity.

### What it forces into existence

None of this exists in Mathlib, which has no discrete Shannon entropy at all.

| | obligation | note |
|---|---|---|
| T1 | `entropy` of a product PMF is the sum of the factors' entropies | where memorylessness cashes out; pure computation |
| T2 | `entropy (μ.map Prod.swap) = entropy μ` | needed because `mutualInfo` must be usable in both coordinate orders — see the D-5 note below |
| T3 | Gibbs' inequality (relative entropy `≥ 0`) | the one analytic ingredient; reachable from `Real.add_one_le_exp`, which Mathlib has |
| T4 | subadditivity `H(Y₁…Yₙ) ≤ Σᵢ H(Yᵢ)` | follows from T3; the only real inequality in the chain |
| T5 | coordinate marginals of a law on `Fin n → X`, and the induced joint on `X × Y` | bookkeeping, but there is a lot of it |
| T6 | `mutualInfo p W ≤ capacity W` for every `p` | `le_csSup` — **this is where S2 is consumed** |

T6 is the concrete link that makes S2 non-optional: bounding anything against a
supremum requires knowing the supremum is not the junk value.

### A friction point created by D-5

`condEntropy μ` is currently `H(A|B)` for `μ : PMF (α × β)`, conditioning on the
*second* coordinate. The chain above needs `H(Yⁿ|Xⁿ)`, i.e. conditioning on the
*first*. So either a swapped variant is added, or T2 is proved and everything is
routed through `Prod.swap`. T2 is the better answer — it also gives symmetry of
`mutualInfo`, which the inclusion–exclusion definition makes nearly free.

Worth confirming during review, since it is a direct consequence of D-5.

### Verdict

Substantial but not risky. Perhaps 300–600 lines. Every piece is standard, and
the pieces are reusable — T1–T4 are exactly the entropy toolkit that S2, S7 and
S8 also need, so the marginal cost of S9 *after* Tier B is much lower than its
cost in isolation. **Sequencing matters more than difficulty here.**

---

## S10 — achievability at a fixed input distribution

```lean
theorem exists_blockCode_of_lt_mutualInfo (W : DMC X Y) (p : PMF X) {ε : ℝ}
    (hR : R < W.mutualInfo p) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ c : BlockCode X Y n,
      (2 : ℝ) ^ ((n : ℝ) * R) ≤ (c.card : ℝ) ∧ c.avgError W ≤ ε
```

### The obstacle is not the mathematics

Two facts about the current Mathlib, both checked:

1. **There is no product of `PMF`s over a `Fintype` index.** No `PMF.pi`. This
   development already hand-rolled the one instance it needed —
   `DMC.power` — as an explicit `PMF.ofFintype` with a normalisation
   obligation. S10 needs two more: the i.i.d. input law `pⁿ`, and the codebook
   ensemble, which is a product of `M` copies of `pⁿ`. A general `PMF.pi` should
   be built once rather than open-coded a third and fourth time.

2. **Mathlib's law of large numbers is measure-theoretic and does not bridge to
   this setting cheaply.** `Mathlib/Probability/StrongLaw.lean` states the
   *strong* law over a measure space (`∀ᵐ ω`, `IdentDistrib`, `MemLp`), and
   Chebyshev (`meas_ge_le_variance_div_sq`) likewise assumes
   `IsFiniteMeasure μ` and `MemLp X 2 μ`. Using either means pushing every `PMF`
   through `PMF.toMeasure` and rebuilding the i.i.d. structure there — which
   cuts against D-11, where finiteness was the reason to stay with `Finset` sums
   and avoid measure theory entirely.

   The alternative is a bespoke Chebyshev bound for finite-alphabet i.i.d. sums.
   Variance is automatically finite on a finite alphabet, so this is elementary
   — but it *is* a self-contained probability development that has to be written.

**This is the real question for S10, and it is a formalization question, not an
information-theory one.**

### Which achievability proof to formalize

The choice materially changes the cost. Roughly, in increasing attractiveness:

- **Joint typicality (Cover & Thomas).** The textbook route. Needs a typicality
  set defined by *three* simultaneous conditions on empirical log-probabilities,
  and hence three concentration estimates plus their union. Most familiar to a
  reader; most expensive to formalize.

- **Feinstein's maximal coding lemma.** Greedy rather than random; gives maximal
  error directly, so no ensemble and no pigeonhole. Attractive, but it delivers
  a *stronger* conclusion than D-1 asks for, and its greedy construction sits
  awkwardly with the deliberate non-constructivity of D-12.

- **Threshold decoding on information density.** Decode to the unique `m` whose
  information density `i(xᵐ;y) = log₂ (W(y|x) / P_Y(y))` exceeds a threshold.
  The error analysis needs **one** concentration statement — a weak law for the
  i.i.d. sum `Σⱼ i(Xⱼ;Yⱼ)`, whose mean is exactly `n·I(p;W)` — plus a
  change-of-measure step for the union bound that is a short computation rather
  than a typicality argument.

**My recommendation is the third**, and I would want it argued rather than
assumed. It collapses the analytic requirement from three concentration
estimates to one, it needs no typicality set at all, and the quantity it
concentrates is the one already central to the statement. It is also the modern
one-shot formulation, so it generalises later without rework.

### Remaining sub-obligations, whichever route is chosen

- A general `PMF.pi` over a `Fintype` index, with the marginal and product-mass
  lemmas that make it usable.
- One weak law of large numbers for finite-alphabet i.i.d. sums — either
  bespoke, or bridged from Mathlib's measure-theoretic version.
- The union bound over the `M − 1` incorrect codewords.
- The pigeonhole step: `(∑ i, μ i · f i ≤ b) → ∃ i, μ i ≠ 0 ∧ f i ≤ b`. Small,
  and it is precisely the step that makes the result non-constructive.
- The decoder as an actual function `(Fin n → Y) → Fin M`, including a
  decidability instance for the decoding rule and a designated failure output.

### A statement-level caution

The statement asserts a code *exists*. Its proof will produce no encoder, and
the ensemble argument gives no way to find one. Nothing downstream — comment,
name, or corollary — should imply otherwise. This is D-12, and it is easiest to
violate accidentally while writing the proof of exactly this lemma.

---

## Questions to take into the discussion

1. **S10 route** — joint typicality, Feinstein, or information-density
   threshold? This is the highest-value decision remaining.
2. **The LLN bridge** — accept measure theory for the concentration step only,
   or write a bespoke finite-alphabet weak law and keep D-11 intact?
3. **`PMF.pi`** — build it properly once, given three call sites are already
   visible? Plausibly upstreamable to Mathlib.
4. **S9 sequencing** — confirm that T1–T4 are built once as a shared entropy
   toolkit serving S2, S7, S8 and S9, rather than per-obligation.
5. **T2 / D-5** — confirm that routing conditional entropy through `Prod.swap`
   is preferred to adding a second `condEntropy` variant.
