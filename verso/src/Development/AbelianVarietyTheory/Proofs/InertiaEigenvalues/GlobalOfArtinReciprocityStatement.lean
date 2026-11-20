import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalOfArtinReciprocity
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGlobalOfArtinReciprocity.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.global_of_artin_reciprocity : GlobalTheory.Published.GlobalArtinReciprocity → StepGlobal := by
  first | exact @GlobalTheory.StepGlobalPf.main | exact GlobalTheory.StepGlobalPf.main | (intros; apply GlobalTheory.StepGlobalPf.main <;> assumption)
