import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisAddHomVanishesComplexConjugation
import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import ReciprocityTheory.NeutralLocalFields.HilbertClassField
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HilbertClassFieldA
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGaloisAddHomVanishesComplexConjugation.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.galoisAddHom_vanishes_complexConjugation : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (M : Type) [AddCommGroup M] [Module O M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    ∀ (c : Ω ≃ₐ[E] Ω), IsComplexConjugation c → z c = 0 := by
  first | exact @GlobalTheory.addHom_complexConjugation_eq_zero | exact GlobalTheory.addHom_complexConjugation_eq_zero | (intros; apply GlobalTheory.addHom_complexConjugation_eq_zero <;> assumption)
