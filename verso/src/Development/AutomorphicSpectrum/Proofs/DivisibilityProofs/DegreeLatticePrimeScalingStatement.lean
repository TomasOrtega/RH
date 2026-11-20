import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DegreeLatticePrimeScaling
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsCompactUnitaryPointsAtPlaceFstMemCompact
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FDegreeLatticePrimeScaling.lean&line=212#L212)
-/
theorem _root_.GlobalTheory.T.degree_lattice_prime_scaling : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω), IsMultiProjPrime (pointIdeal ℤ y) → ∀ (S : Finset Nat.Primes) (b b' : K → ℤ) (s : Ω), s ≠ 0 → (∀ c, segreVec y c ≠ 0 → (∀ t ∈ degLat ℤ y b c, ∃ n : ℕ, ∃ t' ∈ degLat ℤ y b' c, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n * t = s * t') ∧ ∀ t' ∈ degLat ℤ y b' c, ∃ n : ℕ, ∃ t ∈ degLat ℤ y b c, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n * (s * t') = t) → IsHorizontal (pointIdeal ℤ y) → ∃ f g : MRing ι ℤ, (⟨fun _ => b, fun _ => b', fun _ => f, fun _ => g⟩ : LocPair ι ℤ Unit).IsVertOff (pointIdeal ℤ y) S ∧ aeval y f = s * aeval y g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.lineVert_of_eq_off | exact GlobalTheory.CompanionTheory.Ar.Num.lineVert_of_eq_off | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.lineVert_of_eq_off <;> assumption)
