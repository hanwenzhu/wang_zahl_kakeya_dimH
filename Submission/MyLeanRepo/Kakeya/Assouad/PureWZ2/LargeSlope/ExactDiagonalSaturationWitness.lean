import Submission.MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ExactDiagonalGlobalAD
import Submission.MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SaturationPlaneMapExtension

/-!
# Same-cell witnesses for the exact diagonal shading

The final joint target shading is the literal target-grid saturation of the
synchronized exact affine image.  This file exposes that carrierwise
provenance without changing the family or making another spatial selection.
-/

noncomputable section

namespace Kakeya.Assouad

open Set
open PureWZ2ExternalWeightRegularizationData

namespace PureWZ2AffineDiagonalCleanupQuotientAssemblyData

/-- Every point in a final target carrier has an exact-image witness from the
same tube index and the same target grid cell. -/
theorem finalTargetShading_tubeWitness
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (index : Fin assembly.finalTargetSubfamily.family.card)
    (point : Point3)
    (hpoint : point ∈ assembly.finalTargetShading.carrier index) :
    ∃ source : {source : Point3 //
        source ∈ assembly.finalExactShading.carrier index},
      dist point (source : Point3) ≤
        affineScale.targetDelta * Real.sqrt 3 := by
  let sourceFamily := data.selected.family
  let targetFamily :=
    (cleanupTargetSubfamily (cleanup := cleanup) data).family
  have sourcePaperCard :
      (wz1PaperBodyFamily sourceFamily).card = sourceFamily.card := rfl
  have targetFamilyCard : targetFamily.card = sourceFamily.card := rfl
  have targetPaperCard :
      (wz1PaperBodyFamily targetFamily).card = targetFamily.card := rfl
  let targetEquiv : Fin targetFamily.card ≃ Fin sourceFamily.card :=
    (Fin.castOrderIso targetFamilyCard).toEquiv
  let sourceIndex : Fin sourceFamily.card :=
    assembly.joint.finalTargetIndex index
  let sourcePaperIndex : Fin (wz1PaperBodyFamily sourceFamily).card :=
    Fin.cast sourcePaperCard.symm sourceIndex
  let targetIndex : Fin (wz1PaperBodyFamily targetFamily).card :=
    Fin.cast targetPaperCard.symm (targetEquiv.symm sourceIndex)
  have hindex : sourcePaperIndex = targetIndex := by
    apply Fin.ext
    rfl
  have hpointTarget : point ∈
      (cleanupTargetShading (cleanup := cleanup) data).carrier
        targetIndex := by
    change point ∈ (cleanupTargetShading (cleanup := cleanup) data).carrier
      targetIndex at hpoint
    exact hpoint
  have hpointSaturation : point ∈
      wz1PaperCubicalSaturation affineScale.targetDelta
        (pureWZ2AffineDiagonalMapCentered
            affineScale.slopeData.frameSlope cleanup.raw.center
            affineScale.slopeData.heightScale
            affineScale.slopeData.transverseScale 1 ''
          (cleanupTargetSourceShading (regularized := regularized)
            (cleanup := cleanup) data).carrier
              sourcePaperIndex) := by
    rw [hindex]
    rw [← cleanupTargetShading_carrier_eq_saturation
      (regularized := regularized) (cleanup := cleanup) data targetIndex]
    exact hpointTarget
  rcases wz1PaperCubicalSaturation_exists_source_dist_le
      affineScale.targetDelta_pos _ hpointSaturation with
    ⟨source, hsourceImage, hdist⟩
  have hsourceSaturation : source ∈
      wz1PaperCubicalSaturation affineScale.targetDelta
        (pureWZ2AffineDiagonalMapCentered
            affineScale.slopeData.frameSlope cleanup.raw.center
            affineScale.slopeData.heightScale
            affineScale.slopeData.transverseScale 1 ''
          (cleanupTargetSourceShading (regularized := regularized)
            (cleanup := cleanup) data).carrier
              sourcePaperIndex) :=
    ⟨source, hsourceImage, rfl⟩
  have hsourceTargetCanonical : source ∈
      (cleanupTargetShading (cleanup := cleanup) data).carrier
        targetIndex := by
    rw [cleanupTargetShading_carrier_eq_saturation
      (regularized := regularized) (cleanup := cleanup) data targetIndex]
    rw [← hindex]
    exact hsourceSaturation
  have hsourceTarget : source ∈
      assembly.finalTargetShading.carrier index := by
    change source ∈ (cleanupTargetShading (cleanup := cleanup) data).carrier
      targetIndex
    exact hsourceTargetCanonical
  refine ⟨⟨source, ?_⟩, hdist⟩
  change source ∈ (cleanupTargetExactShading
    (regularized := regularized) (cleanup := cleanup) data).carrier
      targetIndex
  rw [cleanupTargetExactShading_carrier
    (regularized := regularized) (cleanup := cleanup) data targetIndex]
  refine ⟨?_, hsourceTargetCanonical⟩
  rw [← hindex]
  exact hsourceImage

/-- Union-level version of the same-cell witness. -/
theorem finalTargetShading_exactWitness
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (point : {point : Point3 // point ∈ assembly.finalTargetShading.union}) :
    ∃ source : {source : Point3 //
        source ∈ assembly.finalExactShading.union},
      dist (point : Point3) (source : Point3) ≤
        affineScale.targetDelta * Real.sqrt 3 := by
  rcases point.property with ⟨index, hpoint⟩
  rcases assembly.finalTargetShading_tubeWitness index point hpoint with
    ⟨source, hdist⟩
  exact ⟨⟨source, ⟨index, source.property⟩⟩, hdist⟩

end PureWZ2AffineDiagonalCleanupQuotientAssemblyData

end Kakeya.Assouad

end
