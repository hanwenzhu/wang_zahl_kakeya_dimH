/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Submission.Kakeya.DimensionThree.MainLemma2.Reduction.SpineGeometricCoreAssembly
public import Submission.Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeSelfHierarchy
public import Submission.Kakeya.MultiScaleSubmult
public import Submission.Kakeya.DimensionThree.MainLemma2.Reduction.SpineTwoScale
public import Submission.Kakeya.DimensionThree.MainLemma2.Reduction.SpineRungWiring
public import Submission.Kakeya.DimensionThree.MainLemma2.LineEssDistinct
public import Submission.Kakeya.Tube.Rigidity
public import Submission.Kakeya.FrostmanTransfer
public import Submission.Kakeya.ShadedUniform
public import Submission.Kakeya.DimensionThree.MainLemma2.GridRounding
public import Submission.Kakeya.StickyKakeya.CrossScale
public import Submission.Kakeya.MultiScaleFac.Stopping
public import Submission.Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeRoute
public import Submission.Kakeya.DimensionThree.MainLemma2.Reduction.SpineDichotomyInputs
public import Submission.Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoarseSeam
public import Submission.Kakeya.MultiScaleFac.UniformBridgeKT

/-!
# The site side of `Kakeya.ML2Core.FourFactorRowsAt`


-/

@[expose] public section

open scoped NNReal

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Core

section Refutation


end Refutation

section CorrectedSupply


end CorrectedSupply

section BallPi


end BallPi

section ParRow


end ParRow

section FineRow

open Classical in
/-- `Kakeya.ShadedTube.translate` and `Tube.translate` agree on the underlying tube. -/
theorem shadedTube_translate_toTube {δ : ℝ≥0} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (S : ShadedTube δ E) (v : E) : (S.translate v).toTube = (S.toTube).translate v := rfl


end FineRow

section CoarseRow


end CoarseRow

section Assembly


end Assembly

section MidRow


/-- **The source's middle-factor scale** `δ̃ = ρ_b/(2 ρ_p)`. -/
noncomputable def midScale (δ : ℝ≥0) (N p b : ℕ) : ℝ≥0 :=
  Tube.gridScale δ N b / (2 * Tube.gridScale δ N p)


end MidRow


section CoarseDensity


end CoarseDensity

section SplitFull

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]


end SplitFull

section SeamSplit


end SeamSplit

section FibreMediant

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]


end FibreMediant

section CoarseWindow


end CoarseWindow

section CardCeilings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]


end CardCeilings

section Producer


end Producer

section AnalyticSupply


end AnalyticSupply

section OuterFork


end OuterFork

section Lead


end Lead

section HandBack


end HandBack

section RowsTie


end RowsTie

section ZeroBallGap


end ZeroBallGap

end Kakeya.ML2Core

end
