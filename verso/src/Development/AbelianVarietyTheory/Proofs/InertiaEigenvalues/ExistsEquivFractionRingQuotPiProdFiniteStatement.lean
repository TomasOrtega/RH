import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivFractionRingQuotPiProdFinite
import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsEquivFractionRingQuotPiProdFinite.lean&line=232#L232)
-/
theorem _root_.GlobalTheory.T.exists_equiv_fractionRingQuot_pi_prod_finite : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ {Y : Type} [AddCommGroup Y] [Module O Y], (∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) →
    Finite (LinearMap.ker (ϖ • LinearMap.id : Y →ₗ[O] Y)) →
    ∃ (a : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Module O F), Finite F ∧ Nonempty (Y ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) := by
  first | exact @GlobalTheory.CofinGen.exists_equiv_pi_prod_finite | exact GlobalTheory.CofinGen.exists_equiv_pi_prod_finite | (intros; apply GlobalTheory.CofinGen.exists_equiv_pi_prod_finite <;> assumption)
