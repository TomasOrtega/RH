import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLabelInertiaEigenvalues
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsLabelInertiaEigenvalues.lean&line=139#L139)
-/
theorem _root_.GlobalTheory.T.exists_label_inertia_eigenvalues : ∀ D : D7, IneRep D → LabDepth D → LabGen D → ∃ Ω : TameOm D, LabIne Ω := by
  first | exact @GlobalTheory.PendOf.LabIneAll.main | exact GlobalTheory.PendOf.LabIneAll.main | (intros; apply GlobalTheory.PendOf.LabIneAll.main <;> assumption)
