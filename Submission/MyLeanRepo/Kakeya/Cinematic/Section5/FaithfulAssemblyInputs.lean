import Submission.MyLeanRepo.Kakeya.Cinematic.WZ2Input
import Submission.MyLeanRepo.Kakeya.Cinematic.Section5.ShadingInputs
import Submission.MyLeanRepo.Kakeya.Cinematic.Section5.FineCarrierMeasurableAssignmentInputs
import Submission.MyLeanRepo.Kakeya.Cinematic.Section5.DyadicPieceVolumeRefinementInputs
import Submission.MyLeanRepo.Kakeya.Cinematic.Section5.PolynomialDyadicPieceRangeInputs
import Submission.MyLeanRepo.Kakeya.Cinematic.Section5.NonThinFineRectangleCountInputs
import Submission.MyLeanRepo.Kakeya.Cinematic.Section5.CoarseFiberCarrierContainmentInputs
import Submission.MyLeanRepo.Kakeya.Cinematic.Section5.CoarseInputs
import Submission.MyLeanRepo.Kakeya.Cinematic.Section5.CoarseCountInputs
import Submission.MyLeanRepo.Kakeya.Cinematic.Section5.ScaleFreeNormalCoarseCountInputs
import Submission.MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs
import Submission.MyLeanRepo.Kakeya.Cinematic.Section5.PolynomialScaleCoarseCountInputs
import Submission.MyLeanRepo.Kakeya.Cinematic.Section5.AmbientBallInputs
import Submission.MyLeanRepo.Kakeya.Cinematic.Section5.PointwiseGoodPairInputs
import Submission.MyLeanRepo.Kakeya.Cinematic.Section5.ProductScalePairIncidenceInputs

/-!
# Faithful short-curve Section 5 assembly boundary

This proposition records the current paper-facing decomposition of the PYZ
Section 5 level-set argument on the centered sixteenth from Lemma 39. The
finite interval-restriction/globalization to the full parameter interval is
kept outside this geometric assembly.
-/

namespace Kakeya.Cinematic

def WZ2ShortCurveLevelSetFromFaithfulInputsStatement : Prop :=
  FineShadingComparisonStatement →
    MaximalFineRectangleSelectionStatement →
    FineCarrierMeasurableAssignmentStatement →
    DyadicPieceVolumeRefinementStatement →
    PolynomialDyadicPieceRangeStatement →
    NonThinFineRectangleCountStatement →
    CoarseFiberCarrierContainmentStatement →
    CommonTangentRectangleStatement →
    FineToCoarseContainmentStatement →
    FineToCoarseCentralStatement →
    FineTangencyLiftToCoarseStatement →
    CoarseRectangleGroupingStatement →
    ComparableCoarseTangencyStatement →
    FiniteAmbientBallCoverStatement →
    Lemma45BadSetBoundsStatement →
    PointwiseGoodPairSelectionStatement →
    CoarseFiberNonconcentrationStatement →
    FinePairIncidenceBoundStatement →
    CoarseMultiplicityInterpolationStatement →
    ProductScaleFixedPairIncidenceStatement →
    FiniteTangentBallCoverStatement →
    FiberwiseSeparatedTangentBallPairAtStatement →
    SharedTangentBallPairPigeonholeAtStatement →
    NormalCoarseRectangleCountStatement →
    ScaleFreeNormalCoarseRectangleCountStatement →
    TangencyGeometryCompletionStatement →
    ComparableRectanglesStatement →
    RectanglePackingStatement →
    ComparabilityTransitivityStatement →
    PolynomialScaleCoarseRectangleCountStatement →
    RectangleSubfamilySelectionStatement →
    RectangleRefinementStatement →
    PolynomialRectangleRefinementStatement →
    BipartiteTangencyRobustFullStatement →
    TwoEndsSelectionStatement →
    TangencyTwoEndsSelectionStatement →
    FineRectangleAssignmentStatement →
    GoodPairCountingStatement →
    PairIncidenceCountingStatement →
    WZ2ShortCurveLevelSetInput

end Kakeya.Cinematic
