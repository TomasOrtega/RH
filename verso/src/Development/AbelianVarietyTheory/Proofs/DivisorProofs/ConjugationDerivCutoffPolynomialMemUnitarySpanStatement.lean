import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugationDerivCutoffPolynomialMemUnitarySpan
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConjugationDerivCutoffPolynomialMemUnitarySpan.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.conjugationDerivCutoffPolynomial_mem_unitarySpan : ∀ {n : ℕ} (ε : Fin n → Bool) (Z : GlobalTheory.PsCo.Pc1.Mat n) (H : ℝ → ℝ) (P : GlobalTheory.PsCo.Pc1.Poly n), GlobalTheory.PsCo.Pc1.IsCutFn H → GlobalTheory.PsCo.Pc1.adBas ε Z H P ∈ GlobalTheory.PsCo.Pc1.AdSpanM ε := by
  first | exact @GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM | exact GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM | (intros; apply GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM <;> assumption)
