import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportDescendedFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMatMemUnitaryGroup
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.descFn_isTest` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsLocallyConstantCompactSupportDescendedFunction.lean&line=4#L4)
-/
theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_descendedFunction : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (j : A.L ≃ₗ[E] (Fin r → E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → IsTest (A.descFn M Ax j lam α f) := by
  first | exact @GlobalTheory.JR.descFn_isTest | exact GlobalTheory.JR.descFn_isTest | (intros; apply GlobalTheory.JR.descFn_isTest <;> assumption)
