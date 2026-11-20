import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCoordinateWedgeLinearIndependentSpanEqTop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
open GlobalTheory GlobalTheory.LogDR

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLogCoordinateWedgeLinearIndependentSpanEqTop.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.logCoordinateWedge_linearIndependent_span_eq_top : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ), IsCoord x → LinearIndependent K (logWedge x) ∧ Submodule.span K (Set.range (logWedge x)) = ⊤ := by
  first | exact @GlobalTheory.LogDR.logWedge_basis | exact GlobalTheory.LogDR.logWedge_basis | (intros; apply GlobalTheory.LogDR.logWedge_basis <;> assumption)
