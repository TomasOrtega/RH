import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointEqOfResidueEqInvertibleOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorsionReduction.eq_of_residue_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorsionPointEqOfResidueEqInvertibleOrder.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.torsion_point_eq_of_residue_eq_invertible_order : ∀ (S : Type) [CommRing S] (P : Out.PolAV (Sp S)) (T : Type) [CommRing T] [IsLocalRing T] (b : S →+* T) (n : ℕ), IsUnit (n : T) → ∀ x y : Over.mk (spMap b) ⟶ P.A, x ^ n = 1 → y ^ n = 1 → spMap (IsLocalRing.residue T) ≫ x.left = spMap (IsLocalRing.residue T) ≫ y.left → x = y := by
  first | exact @GlobalTheory.TorsionReduction.eq_of_residue_eq | exact GlobalTheory.TorsionReduction.eq_of_residue_eq | (intros; apply GlobalTheory.TorsionReduction.eq_of_residue_eq <;> assumption)
