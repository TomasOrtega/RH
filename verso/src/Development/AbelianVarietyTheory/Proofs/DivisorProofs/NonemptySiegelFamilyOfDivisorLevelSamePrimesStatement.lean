import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelFamilyOfDivisorLevelSamePrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonemptySiegelFamilyOfDivisorLevelSamePrimes.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.nonempty_siegelFamily_of_divisor_level_same_primes : ∀ h n N : ℕ, 3 ≤ n → Odd N → n ∣ N → (∃ a, N ∣ n ^ a) → Nonempty (SFam h N (zetaAway N)) → Nonempty (SFam h n (zetaAway n)) := by
  first | exact @GlobalTheory.SiegLev.sFam_down | exact GlobalTheory.SiegLev.sFam_down | (intros; apply GlobalTheory.SiegLev.sFam_down <;> assumption)
