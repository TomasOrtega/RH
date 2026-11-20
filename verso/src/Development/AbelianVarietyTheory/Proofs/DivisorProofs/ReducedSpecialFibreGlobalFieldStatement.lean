import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedSpecialFibreGlobalField
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FReducedSpecialFibreGlobalField.lean&line=94#L94)
-/
theorem _root_.GlobalTheory.T.reduced_special_fibre_global_field : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)), IsProper f → ConnectedSpace (specialFibre f) →
  IsField Γ(reducedSpecialFibre f, ⊤) := by
  first | exact @GlobalTheory.RedFibreField.isField_reducedSpecialFibre | exact GlobalTheory.RedFibreField.isField_reducedSpecialFibre | (intros; apply GlobalTheory.RedFibreField.isField_reducedSpecialFibre <;> assumption)
