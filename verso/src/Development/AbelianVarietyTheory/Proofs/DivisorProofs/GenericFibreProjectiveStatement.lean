import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreProjective
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GenericFibre.isProjOver_genericFibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGenericFibreProjective.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.generic_fibre_projective : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] (q : B ⟶ Sp k) (p : Y ⟶ Sp k), IsProjOver q → IsProjOver p → ∀ (f : Y ⟶ B), f ≫ q = p → ∀ (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → IsProjOver s := by
  first | exact @GlobalTheory.GenericFibre.isProjOver_genericFibre | exact GlobalTheory.GenericFibre.isProjOver_genericFibre | (intros; apply GlobalTheory.GenericFibre.isProjOver_genericFibre <;> assumption)
