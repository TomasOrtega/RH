import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieSpreadFromIdentityPoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHarrisTaylorLieSpreadFromIdentityPoint.lean&line=116#L116)
-/
theorem _root_.GlobalTheory.T.harrisTaylorLie_spread_from_identity_point : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] (tR : R →+* C) (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) → ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp C), x ≫ spMap tR = spMap β → GlobalTheory.UPel.HT.LieAt b act β x := by
  first | exact @GlobalTheory.HTLieSpread.lieAt_spread | exact GlobalTheory.HTLieSpread.lieAt_spread | (intros; apply GlobalTheory.HTLieSpread.lieAt_spread <;> assumption)
