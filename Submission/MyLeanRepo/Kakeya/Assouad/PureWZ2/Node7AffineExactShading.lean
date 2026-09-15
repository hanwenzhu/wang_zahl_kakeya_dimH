import Submission.MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7ExactSlopeCertificate

/-!
# Node 7 exact affine-image shading

This module exposes the unsaturated affine image on the final centered-cleanup
index set.  It stays before every second regularization or quotient step.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

namespace PureWZ2Node7AffineDiagonalPreparationData

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

/-- The selected source shading synchronized with the direct affine target. -/
def sourceExactShading
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    WZ1PaperTubeShading data.sourceRegularization.regularized.selected.family :=
  restrictPaperShading data.sourceRegularization.regularized.selected
    data.popular.popular.restricted

@[simp] theorem sourceExactShading_carrier
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.sourceRegularization.regularized.selected.family.card) :
    data.sourceExactShading.carrier index =
      data.popular.popular.restricted.carrier
        (data.sourceRegularization.regularized.selected.embedding index) :=
  rfl

/-- The source union records exactly the final cleanup indices and no later
regularization or quotient indices. -/
theorem sourceExactShading_union
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.sourceExactShading.union =
      {point | ∃ index : Fin
          data.sourceRegularization.regularized.selected.family.card,
        point ∈ data.popular.popular.restricted.carrier
          (data.sourceRegularization.regularized.selected.embedding index)} := by
  rfl

/-- The synchronized source union is contained in the selected derivative
subband from which the popular box was cut. -/
theorem sourceExactShading_union_subset_subband
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.sourceExactShading.union ⊆ commonSource.subband.shading.union := by
  intro point hpoint
  have hregularized : point ∈
      (restrictPaperShading
        data.sourceRegularization.regularized.selected
        data.popular.popular.restricted).union :=
    hpoint
  have hpopular : point ∈ data.popular.popular.restricted.union :=
    restrictPaperShading_union_subset
      data.sourceRegularization.regularized.selected
      data.popular.popular.restricted hregularized
  exact paperSubshading_union_subset
    data.popular.popular.restricted_subshading hpopular

/-- Carrier-level source provenance with the synchronized ambient index. -/
theorem sourceExactShading_carrier_subset_subband
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.sourceRegularization.regularized.selected.family.card) :
    data.sourceExactShading.carrier index ⊆
      commonSource.subband.shading.carrier
        (data.sourceRegularization.regularized.selected.embedding index) := by
  intro point hpoint
  rw [data.sourceExactShading_carrier index] at hpoint
  exact data.popular.popular.restricted_subshading _ hpoint

/-- The localized target family and the selected source family have the same
cardinality, but keeping this equality explicit avoids relying on semireducible
unfolding across their shading index types. -/
theorem exactShading_family_card
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.selected.localizedFamily.card =
      data.sourceRegularization.regularized.selected.family.card :=
  rfl

/-- Transport a localized target index to the synchronized source family. -/
def exactShadingSourceIndex
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.selected.localizedFamily.card) :
    Fin data.sourceRegularization.regularized.selected.family.card :=
  Fin.cast data.exactShading_family_card index

/-- Transport a localized target index to the ambient paper-family index. -/
def exactShadingAmbientIndex
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.selected.localizedFamily.card) :
    Fin (wz1PaperBodyFamily
      commonSource.commonBand.band.lemma31.data.cfg.family).card :=
  Fin.cast (show
      commonSource.commonBand.band.lemma31.data.cfg.family.card =
        (wz1PaperBodyFamily
          commonSource.commonBand.band.lemma31.data.cfg.family).card by rfl)
    (data.sourceRegularization.regularized.selected.embedding
      (data.exactShadingSourceIndex index))

/-- The selected source carrier at a localized index, retyped to the ambient
paper-family index used by the subband shading. -/
theorem sourceExactShading_carrier_transport
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.selected.localizedFamily.card) :
    data.sourceExactShading.carrier (data.exactShadingSourceIndex index) =
      data.popular.popular.restricted.carrier
        (data.exactShadingAmbientIndex index) := by
  rw [data.sourceExactShading_carrier]
  apply congrArg data.popular.popular.restricted.carrier
  apply Fin.ext
  rfl

/-- The localized target carrier is the public selected carrier at the
transported source index. -/
theorem localizedShading_carrier_transport
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.selected.localizedFamily.card) :
    data.selected.localizedShading.carrier index =
      data.selected.shading.carrier (data.exactShadingSourceIndex index) := by
  change data.selected.shading.carrier
      (data.selected.localizedToPublicIndex index) =
    data.selected.shading.carrier (data.exactShadingSourceIndex index)
  apply congrArg data.selected.shading.carrier
  apply Fin.ext
  rfl

/-- The literal, unsaturated affine image on the direct selected family. -/
def exactShading
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    WZ1PaperTubeShading data.selected.localizedFamily where
  carrier index :=
    pureWZ2AffineDiagonalMapCentered
        data.node7Scale.affineScale.slopeData.frameSlope
        data.selected.center
        data.node7Scale.affineScale.slopeData.heightScale
        data.node7Scale.affineScale.slopeData.transverseScale 1 ''
      data.sourceExactShading.carrier (data.exactShadingSourceIndex index)
  measurable_carrier index := by
    let scale := data.node7Scale.affineScale
    let equivalence := pureWZ2AffineDiagonalAffineEquivCentered
      scale.slopeData.frameSlope data.selected.center
      scale.slopeData.heightScale scale.slopeData.transverseScale 1
      (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
      scale.transverse_pos.ne' one_ne_zero
    have image_eq :
        pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope
              data.selected.center scale.slopeData.heightScale
              scale.slopeData.transverseScale 1 ''
            data.sourceExactShading.carrier
              (data.exactShadingSourceIndex index) =
          equivalence '' data.sourceExactShading.carrier
            (data.exactShadingSourceIndex index) := by
      ext point
      simp only [Set.mem_image]
      constructor
      · rintro ⟨source, hsource, rfl⟩
        exact ⟨source, hsource, by simp [equivalence]⟩
      · rintro ⟨source, hsource, rfl⟩
        exact ⟨source, hsource, by simp [equivalence]⟩
    rw [image_eq]
    exact equivalence.toHomeomorphOfFiniteDimensional.toMeasurableEquiv
      |>.measurableSet_image.mpr
        (data.sourceExactShading.measurable_carrier
          (data.exactShadingSourceIndex index))
  subset_body index := by
    intro point hpoint
    have hsource : point ∈
        pureWZ2AffineDiagonalMapCentered
            data.node7Scale.affineScale.slopeData.frameSlope
            data.selected.center
            data.node7Scale.affineScale.slopeData.heightScale
            data.node7Scale.affineScale.slopeData.transverseScale 1 ''
          data.popular.popular.restricted.carrier
            (data.sourceRegularization.regularized.selected.embedding
              (data.exactShadingSourceIndex index)) := by
      rw [← data.sourceExactShading_carrier
        (data.exactShadingSourceIndex index)]
      exact hpoint
    have hraw := data.selected.exact_image_subset
      (data.exactShadingSourceIndex index) hsource
    have hlocalized : point ∈ data.selected.localizedShading.carrier index := by
      rw [data.localizedShading_carrier_transport index]
      exact hraw
    exact data.selected.localizedShading.subset_body index hlocalized

@[simp] theorem exactShading_carrier
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.selected.localizedFamily.card) :
    data.exactShading.carrier index =
      pureWZ2AffineDiagonalMapCentered
          data.node7Scale.affineScale.slopeData.frameSlope
          data.selected.center
          data.node7Scale.affineScale.slopeData.heightScale
          data.node7Scale.affineScale.slopeData.transverseScale 1 ''
        data.sourceExactShading.carrier
          (data.exactShadingSourceIndex index) :=
  rfl

/-- The exact image is carrierwise contained in the direct saturated shading. -/
theorem exactShading_sub_finalShading
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    PaperIsSubshading data.exactShading data.selected.localizedShading := by
  intro index point hpoint
  rw [data.exactShading_carrier index] at hpoint
  have hsource : point ∈
      pureWZ2AffineDiagonalMapCentered
          data.node7Scale.affineScale.slopeData.frameSlope
          data.selected.center
          data.node7Scale.affineScale.slopeData.heightScale
          data.node7Scale.affineScale.slopeData.transverseScale 1 ''
        data.popular.popular.restricted.carrier
          (data.sourceRegularization.regularized.selected.embedding
            (data.exactShadingSourceIndex index)) := by
    rw [← data.sourceExactShading_carrier
      (data.exactShadingSourceIndex index)]
    exact hpoint
  rw [data.localizedShading_carrier_transport index]
  exact data.selected.exact_image_subset
    (data.exactShadingSourceIndex index) hsource

/-- Union of the exact shading is exactly the affine image of the synchronized
union of the selected source carriers. -/
theorem exactShading_union
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.exactShading.union =
      pureWZ2AffineDiagonalMapCentered
          data.node7Scale.affineScale.slopeData.frameSlope
          data.selected.center
          data.node7Scale.affineScale.slopeData.heightScale
          data.node7Scale.affineScale.slopeData.transverseScale 1 ''
        data.sourceExactShading.union := by
  ext point
  constructor
  · rintro ⟨index, source, hsource, rfl⟩
    exact ⟨source, ⟨data.exactShadingSourceIndex index, hsource⟩, rfl⟩
  · rintro ⟨source, ⟨sourceIndex, hsource⟩, rfl⟩
    let index : Fin data.selected.localizedFamily.card :=
      Fin.cast data.exactShading_family_card.symm sourceIndex
    have hindex : data.exactShadingSourceIndex index = sourceIndex := by
      apply Fin.ext
      rfl
    refine ⟨index, source, ?_, rfl⟩
    rw [hindex]
    exact hsource

/-- Every exact affine-image point has precisely a target height in the
active interval transported from the selected source subband. -/
theorem exactShading_height_mem_active
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.selected.localizedFamily.card)
    (point : Point3)
    (hpoint : point ∈ data.exactShading.carrier index) :
    point 2 ∈ Set.Icc data.activeLeft data.activeRight := by
  rw [data.exactShading_carrier index] at hpoint
  rcases hpoint with ⟨source, hsource, rfl⟩
  have hsourceSubband : source ∈ commonSource.subband.shading.carrier
      (data.exactShadingAmbientIndex index) := by
    apply data.popular.popular.restricted_subshading
    rw [← data.sourceExactShading_carrier_transport index]
    exact hsource
  rw [commonSource.subband.carrier_eq
    (data.exactShadingAmbientIndex index)] at hsourceSubband
  have hheightNonneg :
      0 ≤ data.affineScale.slopeData.heightScale :=
    (lt_of_lt_of_le (by norm_num) data.affineScale.height_lower).le
  have hcenterHeight : data.selected.center 2 =
      data.affineScale.slopeData.anchor := by
    rw [data.selected.center_eq]
    simp [pureWZ2AffineDiagonalCommonCenter, point3]
  rw [pureWZ2AffineDiagonalMapCentered_coord_two, hcenterHeight]
  simp only [one_mul]
  unfold PureWZ2Node7AffineDiagonalPreparationData.activeLeft
    PureWZ2Node7AffineDiagonalPreparationData.activeRight
  exact ⟨mul_le_mul_of_nonneg_left
      (sub_le_sub_right hsourceSubband.2.1 _) hheightNonneg,
    mul_le_mul_of_nonneg_left
      (sub_le_sub_right hsourceSubband.2.2 _) hheightNonneg⟩

/-- Every exact affine-image point lies in the active normalized height
window `[0, 1/2]`. -/
theorem exactShading_active_height
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.selected.localizedFamily.card)
    (point : Point3)
    (hpoint : point ∈ data.exactShading.carrier index) :
    0 ≤ point 2 ∧ point 2 ≤ 1 / 2 := by
  rw [data.exactShading_carrier index] at hpoint
  rcases hpoint with ⟨source, hsource, rfl⟩
  let scale := data.node7Scale.affineScale
  have hsourceSubband : source ∈ commonSource.subband.shading.carrier
      (data.exactShadingAmbientIndex index) := by
    apply data.popular.popular.restricted_subshading
    rw [← data.sourceExactShading_carrier_transport index]
    exact hsource
  rw [commonSource.subband.carrier_eq
    (data.exactShadingAmbientIndex index)] at hsourceSubband
  have hcenterHeight : data.selected.center 2 = commonSource.subband.left := by
    rw [data.selected.center_eq, data.node7Scale.anchor_left]
    simp [pureWZ2AffineDiagonalCommonCenter, point3]
  rw [pureWZ2AffineDiagonalMapCentered_coord_two, hcenterHeight]
  simp only [one_mul]
  constructor
  · exact mul_nonneg (by linarith [scale.height_lower])
      (sub_nonneg.mpr hsourceSubband.2.1)
  · have hheight : source 2 - commonSource.subband.left ≤
        commonSource.subband.right - commonSource.subband.left := by
      linarith [hsourceSubband.2.2]
    rw [commonSource.subband.length_eq, commonSource.commonBand.band.length_eq,
      ← scale.rho_eq] at hheight
    have hheight' : source 2 - commonSource.subband.left ≤
        scale.rho / 5000 := by
      simpa only [show scale.rho / 50 / 100 = scale.rho / 5000 by ring]
        using hheight
    calc
      scale.slopeData.heightScale *
            (source 2 - commonSource.subband.left) ≤
          (2500 / scale.rho) * (scale.rho / 5000) := by
            have hheightUpper : scale.slopeData.heightScale ≤
                2500 / scale.rho := by
              simpa only [scale, data.node7Scale.affineScale.rho_eq] using
                data.node7Scale.height_upper_2500
            exact mul_le_mul hheightUpper hheight'
              (sub_nonneg.mpr hsourceSubband.2.1)
              (div_nonneg (by norm_num) scale.rho_pos.le)
      _ = 1 / 2 := by field_simp [scale.rho_pos.ne']; ring

/-- Union-level active-height certificate used by the following global-AD
transport layer. -/
theorem exactShading_union_active_height
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    {point : Point3} (hpoint : point ∈ data.exactShading.union) :
    point 2 ∈ Set.Icc 0 (1 / 2) := by
  rcases hpoint with ⟨index, hindex⟩
  exact data.exactShading_active_height index point hindex

theorem exactShading_union_height_mem_active
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    {point : Point3} (hpoint : point ∈ data.exactShading.union) :
    point 2 ∈ Set.Icc data.activeLeft data.activeRight := by
  rcases hpoint with ⟨index, hindex⟩
  exact data.exactShading_height_mem_active index point hindex

/-- The exact affine image retains the selected source weight floor on every
final cleanup index. -/
theorem exactShading_mass_lower
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    (ENNReal.ofReal
          data.node7Scale.affineScale.slopeData.rotatedSlopeScale *
        data.sourceRegularization.regularized.selectedWeightLevel) *
        data.selected.localizedFamily.enncard ≤
      data.exactShading.mass := by
  let scale := data.node7Scale.affineScale
  change (ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
        data.sourceRegularization.regularized.selectedWeightLevel) *
      (data.selected.localizedFamily.card : ENNReal) ≤
    ∑ index : Fin data.selected.localizedFamily.card,
      volume (data.exactShading.carrier index)
  calc
    (ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
          data.sourceRegularization.regularized.selectedWeightLevel) *
        (data.selected.localizedFamily.card : ENNReal) =
      ∑ _index : Fin data.selected.localizedFamily.card,
        ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
          data.sourceRegularization.regularized.selectedWeightLevel := by
            simp [Finset.sum_const]
            ring
    _ ≤ ∑ index : Fin data.selected.localizedFamily.card,
        volume (data.exactShading.carrier index) := by
      apply Finset.sum_le_sum
      intro index _
      let sourceIndex := data.exactShadingSourceIndex index
      have hsourceFloor :
          data.sourceRegularization.regularized.selectedWeightLevel ≤
            volume (data.sourceExactShading.carrier sourceIndex) := by
        exact (data.sourceRegularization.regularized.selected_weight_band
          sourceIndex).1
      calc
        ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
              data.sourceRegularization.regularized.selectedWeightLevel ≤
            ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
              volume (data.sourceExactShading.carrier sourceIndex) := by gcongr
        _ = volume (data.exactShading.carrier index) := by
          rw [data.exactShading_carrier index,
            scale.slopeData.heightScale_eq,
            scale.slopeData.transverseScale_eq]
          exact (pureWZ2AffineDiagonalMapCentered_volume_image_general
            scale.slopeData.frameSlope data.selected.center
            scale.slopeData.rotatedSlopeScale_pos
            scale.slopeData.normalizationConstant_pos
            (data.sourceExactShading.measurable_carrier sourceIndex)).symm

end PureWZ2Node7AffineDiagonalPreparationData

end Kakeya.Assouad

end
