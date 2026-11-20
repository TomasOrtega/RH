import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOrigin
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.div_const_origin : GlobalTheory.VertUnits.DivConstOrigin := by
  first | (exact @GlobalTheory.VertUnits.divConstOrigin) | (exact GlobalTheory.VertUnits.divConstOrigin) | (intros; apply GlobalTheory.VertUnits.divConstOrigin <;> assumption)
