import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionEigenOfLocalisedFormsSection
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTypeSpaceProjectionEigenOfLocalisedFormsSection.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.typeSpaceProjectionEigen_of_localisedFormsSection : ∀ D : D7, (∀ i, Nonempty (Sec D i)) → PrType D := by
  first | exact @GlobalTheory.PendOf.PrTypeProof.main | exact GlobalTheory.PendOf.PrTypeProof.main | (intros; apply GlobalTheory.PendOf.PrTypeProof.main <;> assumption)
