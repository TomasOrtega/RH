import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesCoordinateLocallyConstant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PrinTwo.coord_isLC` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrincipalSeriesCoordinateLocallyConstant.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.principal_series_coordinate_locally_constant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), GlobalTheory.PrinTwo.IsLC (GlobalTheory.PrinTwo.coord f) := by
  first | exact @GlobalTheory.PrinTwo.coord_isLC | exact GlobalTheory.PrinTwo.coord_isLC | (intros; apply GlobalTheory.PrinTwo.coord_isLC <;> assumption)
