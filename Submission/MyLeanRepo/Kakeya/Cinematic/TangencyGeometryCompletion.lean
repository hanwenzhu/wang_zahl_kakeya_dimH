import Submission.MyLeanRepo.Kakeya.Cinematic.PreliminaryDichotomy
import Submission.MyLeanRepo.Kakeya.Cinematic.Targets.ConvexTangencySublevelCase
import Submission.MyLeanRepo.Kakeya.Cinematic.Targets.IntervalScaling
import Submission.MyLeanRepo.Kakeya.Cinematic.Targets.TangencyApi
import Submission.MyLeanRepo.Kakeya.Cinematic.Targets.TangencyGeometryAssembly
import Submission.MyLeanRepo.Kakeya.Cinematic.Targets.TangencyIntervalExtension
import Submission.MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelDiameter
import Submission.MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelStructureFromConvex
import Submission.MyLeanRepo.Kakeya.Cinematic.Targets.TwoZeros

/-!
# Closed tangency geometry package

Assemble the completed PYZ Lemmas 13, 14, 16, and 18 into the tangency
geometry certificate consumed by Section 5.
-/

namespace Kakeya.Cinematic

theorem tangency_geometry_completion :
    TangencyGeometryCompletionStatement := by
  have hPreliminary : PreliminaryDichotomyStatement :=
    preliminary_dichotomy
  have hTwoZeros : TwoZerosStatement :=
    cinematic_difference_has_at_most_two_zeros hPreliminary
  have hDiameter : TangencySublevelDiameterStatement :=
    tangency_sublevel_diameter hPreliminary hTwoZeros
  have hSublevel : TangencySublevelStructureStatement :=
    tangency_sublevel_structure_from_convex
      tangency_api interval_scaling_api hDiameter
      convex_tangency_sublevel_case
  exact
    tangency_geometry_assembly hSublevel
      tangency_interval_extension

end Kakeya.Cinematic
