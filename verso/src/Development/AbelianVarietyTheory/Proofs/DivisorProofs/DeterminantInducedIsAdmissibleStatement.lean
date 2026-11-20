import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedIsAdmissible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDeterminantInducedIsAdmissible.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.determinant_induced_isAdmissible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x x' : ℕ) (α β : kˣ →* ℂˣ),
    GlobalTheory.PRep.IsAdmissible (GlobalTheory.ThK.MidJac.detInd x x' α β) := by
  first | exact @GlobalTheory.ThK.MidJac.isAdmissible_detInd | exact GlobalTheory.ThK.MidJac.isAdmissible_detInd | (intros; apply GlobalTheory.ThK.MidJac.isAdmissible_detInd <;> assumption)
