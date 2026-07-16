/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!

# Definition of Regular Ring

Mathlib v4.31 already provides `IsRegularRing`, `isRegularRing_iff`,
`IsRegularRing.of_ringEquiv`, and
`IsRegularLocalRing.of_isRegularRing_of_isLocalRing` in
`Mathlib.RingTheory.RegularLocalRing.Defs` (with `IsRegularRing` extending
`IsNoetherianRing`). This file is kept as a compatibility shim so the
downstream port files can keep their upstream import structure.

-/
