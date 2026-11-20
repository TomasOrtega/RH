import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSpreadsOutFromLocalizationAtPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteSpreadsOutFromLocalizationAtPrime.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.finite_spreads_out_from_localization_at_prime : ∀ (R : Type) [CommRing R] (q : PrimeSpectrum R) (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B], Module.Finite (Localization.AtPrime q.asIdeal) ((Localization.AtPrime q.asIdeal) ⊗[R] B) → ∃ r : R, r ∉ q.asIdeal ∧ Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] B) := by
  first | exact @GlobalTheory.exists_notMem_finite_away_of_finite_atPrime | exact GlobalTheory.exists_notMem_finite_away_of_finite_atPrime | (intros; apply GlobalTheory.exists_notMem_finite_away_of_finite_atPrime <;> assumption)
