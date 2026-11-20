import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoprimeLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
/- English proof (citation)
Apply `GlobalTheory.Models.exists_two_auxiliary_inert_odd_primes_coprime_level` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FCoprimeLevel.lean&line=160#L160)
-/
theorem _root_.GlobalTheory.T.exists_two_inert_odd_primes_coprime_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), (∃ n n' : ℕ, AuxiliaryInertOddPrime H n ∧ AuxiliaryInertOddPrime H n' ∧ n ≠ n') ∧ ∀ n : ℕ, AuxiliaryInertOddPrime H n → ∀ l : Level H, n.Coprime l.M := by
  first | exact @GlobalTheory.Models.exists_two_auxiliary_inert_odd_primes_coprime_level | exact GlobalTheory.Models.exists_two_auxiliary_inert_odd_primes_coprime_level | (intros; apply GlobalTheory.Models.exists_two_auxiliary_inert_odd_primes_coprime_level <;> assumption)
