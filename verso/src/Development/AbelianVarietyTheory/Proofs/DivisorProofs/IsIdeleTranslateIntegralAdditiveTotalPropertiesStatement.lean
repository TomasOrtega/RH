import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdeleTranslateIntegralAdditiveTotalProperties
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
Apply `GlobalTheory.WpFam.TrAdd.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsIdeleTranslateIntegralAdditiveTotalProperties.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.isIdeleTranslateIntegral_additive_total_properties : ∀ (K : Type) [Field K] [NumberField K] (t : (Af K)ˣ), (∀ x x' y y' : K, Tr t x x' → Tr t y y' → Tr t (x - y) (x' - y')) ∧ (∀ (a x x' : K), IsIntegral ℤ a → Tr t x x' → Tr t (a * x) (a * x')) ∧ (∀ x : K, ∃ x', Tr t x x') ∧ (∀ x' : K, ∃ x, Tr t x x') := by
  first | exact @GlobalTheory.WpFam.TrAdd.main | exact GlobalTheory.WpFam.TrAdd.main | (intros; apply GlobalTheory.WpFam.TrAdd.main <;> assumption)
