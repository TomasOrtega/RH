import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedIrreducibleAdmissible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThK.MidJac.detInd_irreducible_admissible` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDeterminantInducedIrreducibleAdmissible.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.determinant_induced_irreducible_admissible : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x x' : ℕ) (α β : kˣ →* ℂˣ), GlobalTheory.KSplit.IsSmU α → GlobalTheory.KSplit.IsSmU β →
    (GlobalTheory.ThK.MidJac.detInd x x' α β).IsIrreducible ∧ GlobalTheory.PRep.IsAdmissible (GlobalTheory.ThK.MidJac.detInd x x' α β) := by
  first | exact @GlobalTheory.ThK.MidJac.detInd_irreducible_admissible | exact GlobalTheory.ThK.MidJac.detInd_irreducible_admissible | (intros; apply GlobalTheory.ThK.MidJac.detInd_irreducible_admissible <;> assumption)
