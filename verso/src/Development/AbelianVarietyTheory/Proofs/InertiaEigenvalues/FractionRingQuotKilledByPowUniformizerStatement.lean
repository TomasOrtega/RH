import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotKilledByPowUniformizer
import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFractionRingQuotKilledByPowUniformizer.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.fractionRingQuot_killed_by_pow_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  first | exact @GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer | exact GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer | (intros; apply GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer <;> assumption)
