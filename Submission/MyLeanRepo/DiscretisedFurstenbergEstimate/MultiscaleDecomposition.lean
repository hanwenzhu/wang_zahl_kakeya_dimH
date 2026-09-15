module

/-
Copyright (c) 2024 The Discretised Furstenberg Estimate Team.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raven Team
-/

public import Submission.MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base
public import Submission.MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.LinearToRegular
public import Submission.MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Root
public import Submission.MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.UniformityBridge

@[expose] public section

/-! # Multiscale Decomposition Framework

This module is split into three submodules:
- `Base`: core definitions and lemmas up to `superlinearToDeltaSSet`
- `LinearToRegular`: the ε-linear → regular dictionary lemma
- `Root`: tube-null lemma, combinatorial Kaufman, and main decomposition theorem
-/
