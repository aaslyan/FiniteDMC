/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import FiniteDMC.Entropy
import FiniteDMC.Channel
import FiniteDMC.Code
import FiniteDMC.Achievability
import FiniteDMC.Converse
import FiniteDMC.Sanity

/-!
# The coding theorem for finite discrete memoryless channels

The scope of this development is exactly: finite input and output alphabets, average block-error
probability, achievability strictly below capacity, and the weak converse.  General or continuous
channels, Shannon-Hartley, zero-error capacity and the strong converse are all out of scope.

See `GOAL.md` for the top-level statements, the draft convention choices, and the current list of
`sorry`s with their classifications.
-/
