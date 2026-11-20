import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetSinhcAdjointUpperRightCoordEqPolJ
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolarU.det_sinhc_eq_polarJacobian` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FDetSinhcAdjointUpperRightCoordEqPolJ.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.det_sinhcAdjointUpperRightCoord_eq_polJ : ∀ (p q : ℕ) (Y : Mat p q), (∀ C : Fin p → Fin q → ℂ, sAd Y (pY C) = pY (sP Y C)) → LinearMap.det (sP Y) = polJ Y := by
  first | exact @GlobalTheory.PolarU.det_sinhc_eq_polarJacobian | exact GlobalTheory.PolarU.det_sinhc_eq_polarJacobian | (intros; apply GlobalTheory.PolarU.det_sinhc_eq_polarJacobian <;> assumption)
