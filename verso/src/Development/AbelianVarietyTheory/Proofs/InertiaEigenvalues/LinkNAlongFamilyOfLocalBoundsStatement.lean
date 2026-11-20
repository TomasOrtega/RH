import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinkNAlongFamilyOfLocalBounds
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLinkNAlongFamilyOfLocalBounds.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.linkN_along_family_of_localBounds : ∀ {eps : ℝ} (Fm : FamP eps), ConclF Fm → Formalism.MainNotions.LinkN Fm := by
  first | exact @GlobalTheory.LinkFam.main | exact GlobalTheory.LinkFam.main | (intros; apply GlobalTheory.LinkFam.main <;> assumption)
