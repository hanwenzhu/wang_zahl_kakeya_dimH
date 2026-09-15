/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Submission.Unconditional.NuminaCoarseRepresentatives
import Submission.Unconditional.IndexedSelection
import Submission.Unconditional.NuminaReanchoredGeometry
import Submission.Unconditional.ReanchoredParentDegree

/-!
# Numina Active Parents

Part of the linking layer that discharges
`StickyKakeya.StickyFrostmanHypothesis`.
-/

noncomputable section

open MeasureTheory

namespace KakeyaLink.JointSelection

open Kakeya.Streamlined Kakeya.Assouad

attribute [local instance] Classical.propDecidable


end KakeyaLink.JointSelection
