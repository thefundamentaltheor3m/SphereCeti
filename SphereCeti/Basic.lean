/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import TauCeti.LinearAlgebra.IntegralLattice.Basic

/-!
# SphereCeti bootstrap check

A minimal use of the pinned TauCeti dependency, proving that the dependency graph declared in
`lakefile.toml` and `lake-manifest.json` actually elaborates on this toolchain.  The roadmap
content replaces this module.
-/

#check @TauCeti.IntegralLattice
