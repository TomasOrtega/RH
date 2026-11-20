import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmIntOfSupLaws
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IntSup.admInt_of_sup` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAdmIntOfSupLaws.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.admInt_of_sup_laws : ∀ (D : D7) (E : IntegralHeckeForms.XD D), SupG D → SupFull D → SupHk D → UnivSup D E → TypeKept E → CommG D → IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E := by
  first | exact @GlobalTheory.IntSup.admInt_of_sup | exact GlobalTheory.IntSup.admInt_of_sup | (intros; apply GlobalTheory.IntSup.admInt_of_sup <;> assumption)
