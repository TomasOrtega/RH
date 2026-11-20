import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterTriangular
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PsType.theta_of_triangular` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FPrincipalSeriesTypeCharacterTriangular.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_triangular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (t : Fin n → kˣ), (∀ i, valuation k (t i : k) = 1) → (∀ i, g.val i i = t i) → ((∀ i j : Fin n, i < j → g.val i j = 0) ∨ ∀ i j : Fin n, j < i → g.val i j = 0) → theta ψ g = ∏ i, (ψ i (t i) : ℂ) := by
  first | exact @GlobalTheory.PsType.theta_of_triangular | exact GlobalTheory.PsType.theta_of_triangular | (intros; apply GlobalTheory.PsType.theta_of_triangular <;> assumption)
