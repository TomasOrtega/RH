import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstCharacterTrivialWildInertiaTypePrime
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ChiTame.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFirstCharacterTrivialWildInertiaTypePrime.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.firstCharacter_trivial_wildInertia_typePrime : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k → ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1 := by
  first | exact @GlobalTheory.ChiTame.main | exact GlobalTheory.ChiTame.main | (intros; apply GlobalTheory.ChiTame.main <;> assumption)
