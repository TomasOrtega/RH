import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicNormalizedWeierstrassValuesCm
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlgebraicitySecondEisenstein.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAlgebraicNormalizedWeierstrassValuesCm.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.algebraic_normalized_weierstrass_values_cm : ∀ (L : PeriodPair) (β Ω : ℂ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → IsAlgebraic ℚ (s2 L / Ω ^ 2) ∧ ∀ (M : ℕ) (P : ℂ), 0 < M → (M : ℂ) * P ∈ L.lattice → IsAlgebraic ℚ (L.weierstrassP P / Ω ^ 2) ∧ IsAlgebraic ℚ (L.derivWeierstrassP P / Ω ^ 3) := by
  first | exact @GlobalTheory.AlgebraicitySecondEisenstein.main | exact GlobalTheory.AlgebraicitySecondEisenstein.main | (intros; apply GlobalTheory.AlgebraicitySecondEisenstein.main <;> assumption)
