/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Submission.Kakeya.Density
public import Submission.Kakeya.FibreCommon
public import Submission.Kakeya.Thickness.ConvexSpaceBody
public import Submission.Kakeya.ChainUniform
public import Submission.Kakeya.Sticky
public import Submission.Kakeya.Uniform
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Submission.Kakeya.Frostman
public import Submission.Kakeya.GridScale
public import Submission.Kakeya.MultiScaleFac.Loss
public import Submission.Kakeya.Tube.Basic
public import Submission.Kakeya.MultiScaleFac.Bridge
public import Submission.Kakeya.MultiScaleLoss
public import Submission.Kakeya.MultiScaleFac.Stopping
public import Submission.Kakeya.MultiScaleFac.UniformBridgeKT
public import Submission.Kakeya.MultiScaleFac.Clump
public import Submission.Kakeya.MultiScaleFac.FibreDensity
public import Submission.Kakeya.Uniform.ParentBodyDensity
public import Submission.Kakeya.Tube.ChainScale
public import Submission.Kakeya.Tube.Nets
public import Submission.Kakeya.KatzTao
public import Submission.Kakeya.Mathlib.Finset
public import Submission.Kakeya.Tube.CardEssentiallyDistinct

/-!
# The gaps between the stopping time and the amended dichotomy, half (B)

The half-(B) counterpart of `Kakeya.MultiScaleFac.GapsA`: the four gap lemmas of the Katz-Tao side,
and the pointwise readings they are assembled from.

Sliced out of the former `DividingScalesKT`.
-/

@[expose] public section

open scoped NNReal ENNReal

open MeasureTheory Real Metric
open scoped Topology NNReal ENNReal

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The four gaps between the stopping time and the amended statement

The statements of this section are the skeleton of the proof of
`Kakeya.MultiScaleFac.dividingScalesKatzTao`. Each one is a single step between what the
Katz-Tao stopping time and its bridge already deliver and what the amended dichotomy displays, and
together with the transports proved earlier in this file they compose to the main theorem. -/

section SsfGapsKT

/-! **The block invariant, the terminal alternative and the homogenization band** now live in
`Kakeya/MultiScaleFac/StoppingKT.lean`, as
`Kakeya.MultiScaleFac.exists_maximal_cutsKT_hoisted_blocks`.  The two obstructions this file
recorded against the statement have been met there: the dimension hypothesis and the threshold have
joined it, and the homogenizing pass now returns a `Kakeya.MultiScaleFac.GridUniform` rather than a
bundle, by way of `Kakeya.MultiScaleFac.exists_gridUniform_restrict_band`.  Moving the declaration
also moved its proof out of this file, which is already too long for the tooling to work in
comfortably. -/


section Pointwise

variable {ι : Type*}


end Pointwise


/-! ### The arithmetic of the displayed losses -/


/-- **The cardinality clause, with the loss raised.**  The stopping time counts in `ℝ≥0∞` against
its own displayed loss; the amended statement displays the common one, and the loss may be raised on
the way. -/
theorem KT.card_le {ι : Type*} {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {B C : ℝ≥0}
    (hB : 1 ≤ B) (hBC : B ≤ C) {K K' c c' : ℕ} (hK : K ≤ K') (hc : c ≤ c')
    {s s' : Finset ι} (h : (s.card : ℝ≥0∞) ≤ totalLoss B K c δ * (s'.card : ℝ≥0∞)) :
    (s.card : ℝ≥0∞) ≤ totalLoss C K' c' δ * (s'.card : ℝ≥0∞) :=
  h.trans (mul_le_mul_left (totalLoss_mono hB hBC hK hc hδ hδ1) _)


/-! ### From one dilated witness to every node of the level -/

section Pointwise

variable {ι : Type*}


end Pointwise


end SsfGapsKT

end MultiScaleFac

end Kakeya

end
