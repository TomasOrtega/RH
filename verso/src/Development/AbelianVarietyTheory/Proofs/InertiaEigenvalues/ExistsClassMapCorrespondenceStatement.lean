import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClassMapCorrespondence
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsClassMapCorrespondence.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.exists_class_map_correspondence : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D), ∃ rc : GlobalTheory.SerSys.Corr D, IsRc hL T I rc ∧ ∀ k v, IsClassMap D.naut.lpDim (rc k v) := by
  first | exact @GlobalTheory.TypeRec.exists_isRc_isClassMap | exact GlobalTheory.TypeRec.exists_isRc_isClassMap | (intros; apply GlobalTheory.TypeRec.exists_isRc_isClassMap <;> assumption)
