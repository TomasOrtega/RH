import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftMonoOfFpqcCoverLift
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLiftMonoOfFpqcCoverLift.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_lift_mono_of_fpqc_cover_lift : ∀ (G T T' Y : Scheme.{0}) (π : G ⟶ Y) [Mono π] (y : T ⟶ Y) (t : T' ⟶ T) [Flat t] [Surjective t] [QuasiCompact t] (z : T' ⟶ G), z ≫ π = t ≫ y → ∃ w : T ⟶ G, w ≫ π = y := by
  first | exact @GlobalTheory.DualOpen.exists_lift_of_fpqc_cover | exact GlobalTheory.DualOpen.exists_lift_of_fpqc_cover | (intros; apply GlobalTheory.DualOpen.exists_lift_of_fpqc_cover <;> assumption)
