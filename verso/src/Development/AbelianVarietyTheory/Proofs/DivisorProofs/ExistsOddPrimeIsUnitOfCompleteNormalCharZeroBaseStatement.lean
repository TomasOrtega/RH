import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddPrimeIsUnitOfCompleteNormalCharZeroBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_odd_prime_isUnit_of_base` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsOddPrimeIsUnitOfCompleteNormalCharZeroBase.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.exists_odd_prime_isUnit_of_completeNormalCharZeroBase : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : R) := by
  first | exact @GlobalTheory.exists_odd_prime_isUnit_of_base | exact GlobalTheory.exists_odd_prime_isUnit_of_base | (intros; apply GlobalTheory.exists_odd_prime_isUnit_of_base <;> assumption)
