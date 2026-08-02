# FiniteDMC — the coding theorem for finite discrete memoryless channels

A Lean 4 / Mathlib formalization of the channel coding theorem for **finite
discrete memoryless channels**: finite input and output alphabets, average
block-error probability, achievability strictly below capacity, and the weak
converse.

Explicitly **out of scope**: general or continuous channels, Shannon–Hartley,
zero-error capacity, and the strong converse. None of those belong in this
repository unless a separate, later decision says otherwise.

## Status

**The coding theorem is proved**, in both directions. `lake build` succeeds with
no `sorry` and no warnings, and both top-level theorems depend only on the three
standard Mathlib axioms:

```
'FiniteDMC.coding_achievability' : [propext, Classical.choice, Quot.sound]
'FiniteDMC.weak_converse'        : [propext, Classical.choice, Quot.sound]
```

Notably, the development needs **no measure theory** — everything is `Finset`
sums over finite types, including the law of large numbers. Mathlib has no
discrete Shannon entropy, so that layer is built here from `Real.log_le_sub_one_of_pos`
alone, with no appeal to Jensen or convexity.

**No convention is settled.** See [`GOAL.md`](GOAL.md) for the statements, the
draft convention choices, and the `sorry` list; and
[`HARD-PARTS.md`](HARD-PARTS.md) for the two obligations that need a decision
before they are attempted.

## Layout

| file | contents |
|------|----------|
| `FiniteDMC/Entropy.lean` | Shannon entropy, conditional entropy, mutual information on a `Fintype` (Mathlib has none of these) |
| `FiniteDMC/EntropyBounds.lean` | non-negativity, Gibbs' inequality, the maximum-entropy bound |
| `FiniteDMC/Channel.lean` | `DMC`, the memoryless `n`-fold extension, mutual information across a channel, capacity as a supremum |
| `FiniteDMC/Code.lean` | `BlockCode`, rate, conditional and average error, the induced joint laws |
| `FiniteDMC/RandomCoding.lean` | `PMF.pi`, the information density, and the decomposition of achievability |
| `FiniteDMC/Achievability.lean` | the direct theorem |
| `FiniteDMC/Converse.lean` | the one-shot Fano bound and the weak converse |
| `FiniteDMC/Sanity.lean` | closed, `sorry`-free checks that the conventions are what they claim |

## Building

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

Toolchain: Lean 4.32.2, Mathlib v4.32.2.
