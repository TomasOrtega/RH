import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityTensorAinfCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFrobeniusIntegralityTensorAinfCoefficients.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.frobenius_integrality_tensor_ainf_coefficients : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (RW LL)) (S : Matrix p p (RA LL)) (S' : Matrix q q (RA LL)) (Y : Matrix p q (RA LL)), Z.map (φRW LL) = S.map (inclR LL) * Z * S'.map (inclR LL) + Y.map (inclR LL) → ∀ a b, Z a b ∈ Set.range (inclR LL) := by
  first | exact @GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff | exact GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff | (intros; apply GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff <;> assumption)
