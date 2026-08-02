# FiniteDMC — the coding theorem for finite discrete memoryless channels

A Lean 4 / Mathlib formalization of the channel coding theorem for **finite
discrete memoryless channels**: finite input and output alphabets, average
block-error probability, achievability strictly below capacity, and the weak
converse.

Explicitly **out of scope**: general or continuous channels, Shannon–Hartley,
zero-error capacity, and the strong converse. None of those belong in this
repository unless a separate, later decision says otherwise.

## Status

Statements and dependency graph only. `lake build` succeeds; there are 11 named,
precisely typed `sorry`s. Both top-level theorems are fully proved *from* those
`sorry`s — the connecting arguments are real proofs.

**No individual `sorry` has been attempted, and no convention is settled.** See
[`GOAL.md`](GOAL.md) for the statements, the draft convention choices, and the
`sorry` list with classifications; it is the artifact under review.

## Layout

| file | contents |
|------|----------|
| `FiniteDMC/Entropy.lean` | Shannon entropy, conditional entropy, mutual information on a `Fintype` (Mathlib has none of these) |
| `FiniteDMC/Channel.lean` | `DMC`, the memoryless `n`-fold extension, mutual information across a channel, capacity as a supremum |
| `FiniteDMC/Code.lean` | `BlockCode`, rate, conditional and average error, the induced joint laws |
| `FiniteDMC/Achievability.lean` | the direct theorem |
| `FiniteDMC/Converse.lean` | the one-shot Fano bound and the weak converse |
| `FiniteDMC/Sanity.lean` | closed, `sorry`-free checks that the conventions are what they claim |

## Building

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

Toolchain: Lean 4.32.2, Mathlib v4.32.2.
