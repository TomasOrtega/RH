import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldIsAlgebraicAdjoinJInvariant
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
Apply `GlobalTheory.FN.frac_isAlgebraic_adjoin_j` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FFractionFieldIsAlgebraicAdjoinJInvariant.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.fractionField_isAlgebraic_adjoin_jInvariant : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : GlobalTheory.FN.ring ε.range), (a : ℍ → ℂ) = jT → ∀ f : T.K, IsAlgebraic (IntermediateField.adjoin Ω {T.io a}) f := by
  first | exact @GlobalTheory.FN.frac_isAlgebraic_adjoin_j | exact GlobalTheory.FN.frac_isAlgebraic_adjoin_j | (intros; apply GlobalTheory.FN.frac_isAlgebraic_adjoin_j <;> assumption)
