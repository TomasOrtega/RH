import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlaceOfOverTypePrime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TypeSplit.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsSplitPlaceOfOverTypePrime.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.isSplitPlace_of_over_type_prime : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k), IsSplitPl D.host w := by
  first | exact @GlobalTheory.TypeSplit.main | exact GlobalTheory.TypeSplit.main | (intros; apply GlobalTheory.TypeSplit.main <;> assumption)
