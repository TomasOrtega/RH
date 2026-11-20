import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InterpChgSmooth.smooth_phR` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTruncatedPotentialSmooth.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.truncated_potential_smooth : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∀ c u σ (R : ℝ), 2 ≤ R → ((T.M c).A σ).Smooth ((T.F c).phR R u σ) := by
  first | exact @GlobalTheory.InterpChgSmooth.smooth_phR | exact GlobalTheory.InterpChgSmooth.smooth_phR | (intros; apply GlobalTheory.InterpChgSmooth.smooth_phR <;> assumption)
