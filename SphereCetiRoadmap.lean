/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCetiRoadmap.CoefficientMagic.Comparison
public import SphereCetiRoadmap.CoefficientMagic.Geometry
public import SphereCetiRoadmap.CoefficientMagic.Suggested
public import SphereCetiRoadmap.Suggested

/-!
# SphereCeti roadmap target library

This separately built library is reserved for the target signatures in the mathematical roadmap.
It may import the SphereCeti library; the SphereCeti library must not import roadmap targets.
The target signatures in `Suggested.lean` belong to the mathematical roadmap in README.md.  Those in
`CoefficientMagic/` belong to the sibling roadmap in `CoefficientMagic/README.md`, which README.md
incorporates: `CoefficientMagic.Suggested` is its core, and `CoefficientMagic.Comparison` and
`CoefficientMagic.Geometry` import that core.
-/
