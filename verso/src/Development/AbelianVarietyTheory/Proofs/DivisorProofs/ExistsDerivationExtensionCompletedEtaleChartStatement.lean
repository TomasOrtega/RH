import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtensionCompletedEtaleChart
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ChartDerivation.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsDerivationExtensionCompletedEtaleChart.lean&line=179#L179)
-/
theorem _root_.GlobalTheory.T.exists_derivation_extension_completedEtaleChart : ∀ (A : Type) [CommRing A] [IsLocalRing A] (k : Type) [Field k] [CharZero k] (m d : ℕ) (ψ : A →+* ChartRing k m d), IsEtaleCompletion ψ → ∀ δ : Derivation ℤ A A, ∃ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), ∀ a, D' (ψ a) = ψ (δ a) := by
  first | exact @GlobalTheory.ChartDerivation.main | exact GlobalTheory.ChartDerivation.main | (intros; apply GlobalTheory.ChartDerivation.main <;> assumption)
