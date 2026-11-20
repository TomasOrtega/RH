import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexBoundParameterRequirementsEventuallyFamily
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OnWithOfIsEmpty
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OntoSizeRows.sizeRows_along` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIndexBoundParameterRequirementsEventuallyFamily.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.indexBoundParameterRequirements_eventually_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x, GlobalTheory.IndexAssembly.SizeRows (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def := by
  first | exact @GlobalTheory.OntoSizeRows.sizeRows_along | exact GlobalTheory.OntoSizeRows.sizeRows_along | (intros; apply GlobalTheory.OntoSizeRows.sizeRows_along <;> assumption)
