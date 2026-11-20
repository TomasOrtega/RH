import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiKMulNLEqOneOnIntegralLattice
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.NormInt.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPsiKMulNLEqOneOnIntegralLattice.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.psiK_mul_NL_eq_one_on_integral_lattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y : A.L, (∀ i, ‖j y i‖ ≤ 1) → A.psiK ψ (x * A.NL y) = 1 := by
  first | exact @GlobalTheory.JR.NormInt.main | exact GlobalTheory.JR.NormInt.main | (intros; apply GlobalTheory.JR.NormInt.main <;> assumption)
