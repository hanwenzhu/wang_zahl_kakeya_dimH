import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushHomogeneousSmallScale
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushAmbientMultiplicityCore
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushAmbientIncidence
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushHomogeneousTwoEnds
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushHomogeneousParameterSelection
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushHomogeneousLowDensity
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushHomogeneousScaleDichotomy
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushAmbientStemSelection
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushOrientedAngleBand
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushHomogeneousFarRadius
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushAsymmetricFarShading
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushHomogeneousOrientedFarShading
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushOrientedFamilyTransfer
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushAsymmetricFixedStemCordoba
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushCordobaDenominatorAbsorption
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushHomogeneousCordobaGeometry
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushHomogeneousHardPower
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushLocalNumericalClosure
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushSelfContainedFiberAssembly
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushPreprocessing
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushLabeledAngularStopping
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushCoarseTubeIncidenceGrouping
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushCoarseTubeKatzTaoCardinality
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushSlabGroupBalancing
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushBalancedFrostmanCount
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushBalancedGroupSummation
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.HairbrushSelfContainedExpandedAssembly
import Submission.MyLeanRepo.Kakeya.Assouad.Targets.Proposition1_8Assembly

/-!
# Standalone Assertion D at (1/2, 0)

This module extracts the unconditional hairbrush assembly from
`SubunitAdmissibleCeiling.lean` into a named theorem.

The proof applies the ~24 closed hairbrush leaves through the
self-contained fiber and expanded assemblies, then converts to the
exact `Kakeya.AssertionD (1/2) 0` API via `proposition1_8_assembly`.
-/

namespace Kakeya.Assouad

/-- The hairbrush theorem at exponent 1/2, assembled from closed leaves. -/
theorem assertionD_one_half_zero : Kakeya.AssertionD (1 / 2) 0 := by
  have h_fiber : HairbrushSelfContainedFiberEstimateStatement :=
    hairbrush_self_contained_fiber_assembly
      hairbrush_homogeneous_small_scale
      hairbrush_ambient_multiplicity_core
      hairbrush_ambient_incidence
      hairbrush_homogeneous_two_ends
      hairbrush_homogeneous_parameter_selection
      hairbrush_homogeneous_low_density
      hairbrush_homogeneous_scale_dichotomy
      hairbrush_ambient_stem_selection
      hairbrush_oriented_angle_band
      hairbrush_homogeneous_far_radius
      hairbrush_asymmetric_far_shading
      hairbrush_homogeneous_oriented_far_shading
      hairbrush_oriented_family_transfer
      hairbrush_asymmetric_fixed_stem_cordoba
      hairbrush_cordoba_denominator_absorption
      hairbrush_homogeneous_cordoba_geometry
      hairbrush_homogeneous_hard_power
      hairbrush_local_numerical_closure
  have h_expanded : HairbrushExpandedEstimate :=
    hairbrush_self_contained_expanded_assembly
      hairbrush_preprocessing
      hairbrush_labeled_angular_stopping
      hairbrush_coarse_tube_incidence_grouping
      hairbrush_coarse_tube_katz_tao_cardinality
      hairbrush_slab_group_balancing
      hairbrush_balanced_frostman_count
      hairbrush_balanced_group_summation
      h_fiber
  exact proposition1_8_assembly h_expanded

end Kakeya.Assouad
