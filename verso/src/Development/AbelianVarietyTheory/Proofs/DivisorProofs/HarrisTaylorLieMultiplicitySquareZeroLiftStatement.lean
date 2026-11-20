import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieMultiplicitySquareZeroLift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTLiftLie.lieMult_of_sqZeroLift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHarrisTaylorLieMultiplicitySquareZeroLift.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.harrisTaylor_lieMultiplicity_squareZeroLift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i) (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp C) (β : R →+* k), x ≫ spMap tR = spMap β → ∀ j, LieMult (act.toF D) x (β.comp (b.t j)) D.m := by
  first | exact @GlobalTheory.HTLiftLie.lieMult_of_sqZeroLift | exact GlobalTheory.HTLiftLie.lieMult_of_sqZeroLift | (intros; apply GlobalTheory.HTLiftLie.lieMult_of_sqZeroLift <;> assumption)
