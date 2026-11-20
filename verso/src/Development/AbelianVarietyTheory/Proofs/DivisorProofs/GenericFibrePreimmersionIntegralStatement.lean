import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePreimmersionIntegral
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGenericFibrePreimmersionIntegral.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.generic_fibre_preimmersion_integral : ∀ (B Y : Scheme.{0}) [IsIntegral B] (f : Y ⟶ B) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → IsPreimmersion j ∧ Set.range j = f ⁻¹' {genericPoint B} ∧ (∀ x : G, IsIso (j.stalkMap x)) ∧ ∀ [IsIntegral Y], Nonempty G → ∃ _ : IsIntegral G, j (genericPoint G) = genericPoint Y := by
  first | exact @GlobalTheory.GenericFibreGeom.genericFibre_props | exact GlobalTheory.GenericFibreGeom.genericFibre_props | (intros; apply GlobalTheory.GenericFibreGeom.genericFibre_props <;> assumption)
