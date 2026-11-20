import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAlgClosedResidueFieldValuedField
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlphaPair.ResField.exists_residueField` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FExistsAlgClosedResidueFieldValuedField.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.exists_algClosed_residueField_valuedField : ∀ (C : Type) [Field C] (V : VF C), IsAlgClosed C → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharP Ω V.l) (ρ : V.RR →+* Ω), ∀ x : V.RR, ρ x = 0 ↔ V.MM (x : C) := by
  first | exact @GlobalTheory.AlphaPair.ResField.exists_residueField | exact GlobalTheory.AlphaPair.ResField.exists_residueField | (intros; apply GlobalTheory.AlphaPair.ResField.exists_residueField <;> assumption)
