# FiniteDMC — the coding theorem for finite discrete memoryless channels

A Lean 4 / Mathlib formalization of the channel coding theorem for **finite
discrete memoryless channels**: finite input and output alphabets, average
block-error probability, achievability strictly below capacity, and the weak
converse.

Explicitly **out of scope**: general or continuous channels, Shannon–Hartley,
zero-error capacity, and the strong converse. None of those belong in this
repository unless a separate, later decision says otherwise.

## Status

`lake build` succeeds. **The weak converse is proved** — unconditionally, with no
`sorry` anywhere beneath it, in both its `R`-form and its `limsup`-form.

**Two** `sorry`s remain, both inside achievability: the random-coding bound
itself and the weak law of large numbers it needs. Achievability's assembly —
including the message-count bookkeeping — is proved from those two.

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
