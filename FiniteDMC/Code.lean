/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import FiniteDMC.Channel
import Mathlib.Probability.Distributions.Uniform

/-!
# Fixed-length block codes for a finite DMC

A block code of length `n` is a message set together with a deterministic encoder and a
deterministic decoder.

## Main definitions

* `FiniteDMC.BlockCode X Y n` : a fixed-length block code, with `c.card` messages.
* `FiniteDMC.BlockCode.rate c` : `log₂ c.card / n`, in bits per channel use.
* `FiniteDMC.BlockCode.condError c W m` : the probability of a decoding error given message `m`.
* `FiniteDMC.BlockCode.avgError c W` : the average (over uniform messages) error probability.
* `FiniteDMC.BlockCode.messageDist c` : the uniform distribution on messages.
* `FiniteDMC.BlockCode.msgOutJoint c W` : the joint law of `(message, output block)`.
* `FiniteDMC.BlockCode.inOutJoint c W` : the joint law of `(input block, output block)`.

## Implementation notes

* **The message set is `Fin c.card`, not an abstract `Fintype`.**  Every asymptotic statement in
  this development compares a *natural number* of messages against a *real* `2 ^ (n * R)`; keeping
  the message count as a bare `ℕ` field means that comparison is stated one way, in one place,
  rather than mediated by `Fintype.card` at each use.  See `GOAL.md` (decision D-8).
* **A code does not mention the channel.**  `BlockCode X Y n` depends only on the alphabets, which
  is what a code actually is; the channel enters only through `condError` / `avgError`.  See
  `GOAL.md` (decision D-9).
* **Error probability is a `Finset` sum, not a measure.**  Everything in sight is a `Fintype`, so
  `∑ y, if decode y = m then 0 else Wⁿ y` avoids dragging in `PMF.toMeasure`.
-/

namespace FiniteDMC

open Finset

variable {X Y : Type*} [Fintype X] [Fintype Y] {n : ℕ}

/-- A fixed-length block code of length `n` for alphabets `X` and `Y`: `card` messages, a
deterministic encoder into length-`n` input blocks, and a deterministic decoder from length-`n`
output blocks. -/
structure BlockCode (X Y : Type*) [Fintype X] [Fintype Y] (n : ℕ) where
  /-- The number of messages. -/
  card : ℕ
  /-- There is at least one message, so that the uniform message law exists. -/
  card_pos : 0 < card
  /-- The encoder. -/
  encode : Fin card → Fin n → X
  /-- The decoder. -/
  decode : (Fin n → Y) → Fin card

namespace BlockCode

variable (c : BlockCode X Y n) (W : DMC X Y)

/-- The message set of a block code is nonempty. -/
theorem nonempty_fin : Nonempty (Fin c.card) := ⟨⟨0, c.card_pos⟩⟩

/-- The rate `log₂ c.card / n` of a block code, in bits per channel use. -/
noncomputable def rate : ℝ := Real.logb 2 c.card / n

/-- The probability that the decoder does not return `m` when `m` was sent. -/
noncomputable def condError (m : Fin c.card) : ℝ :=
  ∑ y : Fin n → Y, if c.decode y = m then 0 else ((W.power n).transition (c.encode m) y).toReal

/-- The average error probability of a block code, the message being uniform. -/
noncomputable def avgError : ℝ :=
  (c.card : ℝ)⁻¹ * ∑ m : Fin c.card, c.condError W m

/-- The uniform distribution on the message set. -/
noncomputable def messageDist : PMF (Fin c.card) :=
  haveI := c.nonempty_fin
  PMF.uniformOfFintype (Fin c.card)

/-- The channel from messages to output blocks induced by a code: encode, then transmit.

Presenting the code this way lets the whole joint-law and mutual-information API for `DMC` be
reused verbatim on the message-to-output link. -/
noncomputable def codeChannel : DMC (Fin c.card) (Fin n → Y) where
  transition m := (W.power n).transition (c.encode m)

@[simp]
theorem codeChannel_transition (m : Fin c.card) :
    (c.codeChannel W).transition m = (W.power n).transition (c.encode m) := rfl

/-- The joint law of the transmitted message and the received block, the message being uniform. -/
noncomputable def msgOutJoint : PMF (Fin c.card × (Fin n → Y)) :=
  (c.codeChannel W).joint c.messageDist

/-- The joint law of the transmitted input block and the received block, the message being
uniform. -/
noncomputable def inOutJoint : PMF ((Fin n → X) × (Fin n → Y)) :=
  (W.power n).joint (c.messageDist.map c.encode)

end BlockCode

end FiniteDMC
