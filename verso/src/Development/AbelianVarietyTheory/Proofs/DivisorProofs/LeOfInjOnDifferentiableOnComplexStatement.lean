import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfInjOnDifferentiableOnComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLeOfInjOnDifferentiableOnComplex.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.le_of_injOn_differentiableOn_complex : ∀ (d d' : ℕ) (U : Set (Fin d → ℂ)) (f : (Fin d → ℂ) → (Fin d' → ℂ)), IsOpen U → U.Nonempty → DifferentiableOn ℂ f U → Set.InjOn f U → d ≤ d' := by
  first | exact @GlobalTheory.InjHol.le_of_injOn_differentiableOn | exact GlobalTheory.InjHol.le_of_injOn_differentiableOn | (intros; apply GlobalTheory.InjHol.le_of_injOn_differentiableOn <;> assumption)
