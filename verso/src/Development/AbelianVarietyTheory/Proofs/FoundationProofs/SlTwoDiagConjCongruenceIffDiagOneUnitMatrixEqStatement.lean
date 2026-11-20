import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceIffDiagOneUnitMatrixEq
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FNCong.cong_iff_dg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSlTwoDiagConjCongruenceIffDiagOneUnitMatrixEq.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq : ∀ (N : ℕ) (d : ℤ) (u : (ZMod N)ˣ), (u : ZMod N) = d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' ↔ dg u * redGL N γ' = redGL N γ * dg u := by
  first | exact @GlobalTheory.FNCong.cong_iff_dg | exact GlobalTheory.FNCong.cong_iff_dg | (intros; apply GlobalTheory.FNCong.cong_iff_dg <;> assumption)
