import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndexBoundCoefficientFieldOfExactSmallField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldTies
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIndexBoundCoefficientFieldOfExactSmallField.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.fieldTies_of_rayField_of_ksExact : GlobalTheory.NT.RayField → ∀ (X : Stages) (f : Fr X.B.toPre) (δ : Fld.FieldDat X.B.toPre), X.B.KsExact δ f → FieldTies X.toD7 (Fr.at X f) := by
  first | exact @GlobalTheory.AtMember.fieldTies_of_ksExact | exact GlobalTheory.AtMember.fieldTies_of_ksExact | (intros; apply GlobalTheory.AtMember.fieldTies_of_ksExact <;> assumption)
