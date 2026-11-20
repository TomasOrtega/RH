import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyDeeperLevelOfDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SiegLev.sFam_of_dvd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSiegelFamilyDeeperLevelOfDvd.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.siegelFamily_deeper_level_of_dvd : ∀ (h n N : ℕ) (o : Type) [CommRing o] [IsNoetherianRing o] (b : TBase o N), 3 ≤ n → Odd N → n ∣ N → Nonempty (SFam h n ((b.ζ : o) ^ (N / n))) → Nonempty (SFam h N (b.ζ : o)) := by
  first | exact @GlobalTheory.SiegLev.sFam_of_dvd | exact GlobalTheory.SiegLev.sFam_of_dvd | (intros; apply GlobalTheory.SiegLev.sFam_of_dvd <;> assumption)
