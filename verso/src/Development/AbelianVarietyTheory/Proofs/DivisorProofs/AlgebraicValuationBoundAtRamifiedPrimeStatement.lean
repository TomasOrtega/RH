import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationBoundAtRamifiedPrime
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
Apply `GlobalTheory.SzRamified.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAlgebraicValuationBoundAtRamifiedPrime.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.algebraicValuation_bound_at_ramified_prime : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (w σ p : ℂ), 4 < l → w ^ 2 = -(l : ℂ) → Sz l lam 0 (12 * p) → Sz l lam 0 (((1 + w) ^ 2 - (1 + (l : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) → Sz l lam (1 / 2) σ := by
  first | exact @GlobalTheory.SzRamified.main | exact GlobalTheory.SzRamified.main | (intros; apply GlobalTheory.SzRamified.main <;> assumption)
