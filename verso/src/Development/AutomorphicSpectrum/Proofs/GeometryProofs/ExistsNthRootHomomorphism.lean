import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsFactorThroughMultiplication
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `PositivityTheory.Xgf.exists_nth_root_homomorphism` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FSesquilinearFractions%2FExistsFactorThroughMultiplication.lean&line=111#L111)
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_nth_root_homomorphism : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (n : ℕ) (A B : Out.PolAV (Sp (𝓞 K))) (f : A.A ⟶ B.A), IsMonHom f → 0 < n → (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.A, x ^ n = 1 → x ≫ f = 1) → ∃ f' : A.A ⟶ B.A, IsMonHom f' ∧ f' ^ n = f := by
  first | exact @PositivityTheory.Xgf.exists_nth_root_homomorphism | exact PositivityTheory.Xgf.exists_nth_root_homomorphism
