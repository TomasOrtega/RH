import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqEulerCharacteristic
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GenericFibreDegree.chi_eq_residueDegree` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FResidueDegreeEqEulerCharacteristic.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.residue_degree_eq_euler_characteristic : ∀ (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (f : Y ⟶ B) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → IsProjOver s → topologicalKrullDim G ≤ (0 : ℕ) → Nonempty G → f.residueDegree (genericPoint Y) ≠ 0 ∧ (letI := algebraΓOfHom s; chi B.functionField (structureModule G)) = f.residueDegree (genericPoint Y) := by
  first | exact @GlobalTheory.GenericFibreDegree.chi_eq_residueDegree | exact GlobalTheory.GenericFibreDegree.chi_eq_residueDegree | (intros; apply GlobalTheory.GenericFibreDegree.chi_eq_residueDegree <;> assumption)
