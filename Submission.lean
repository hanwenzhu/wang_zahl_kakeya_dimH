import ChallengeDeps
import Submission.Helpers
import Submission.Unconditional.KakeyaConjecture

open LeanEval.Analysis.WangZahlKakeya
open MeasureTheory

namespace Submission

theorem wang_zahl_kakeya_dimH {K : Set Space} (hK : IsKakeya K) :
    dimH K = 3 := by
  apply Unconditional.KakeyaDimensionThree K
  refine ⟨hK.1, ?_⟩
  intro v hv
  obtain ⟨x, hx⟩ := hK.2 v hv
  refine ⟨x, ?_⟩
  rw [affineSegment]
  rintro _ ⟨t, ht, rfl⟩
  simpa [AffineMap.lineMap_apply_module', add_comm] using hx t ht

end Submission

#print axioms Submission.wang_zahl_kakeya_dimH
