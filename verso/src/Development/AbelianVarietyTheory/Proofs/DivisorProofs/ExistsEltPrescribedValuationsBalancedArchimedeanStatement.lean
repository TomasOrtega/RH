import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEltPrescribedValuationsBalancedArchimedean
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovHt.exists_elt_balanced` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsEltPrescribedValuationsBalancedArchimedean.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.exists_elt_prescribed_valuations_balanced_archimedean : ∀ (K : Type) [Field K] [NumberField K] (e : HeightOneSpectrum (𝓞 K) →₀ ℝ) (t : (K →+* ℂ) → ℝ), (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → ∃ C : ℝ, ∀ τ : ℕ, ∃ α : K, α ≠ 0 ∧ (∀ la, (τ : ℝ) * e la ≤ (vLa la α : ℝ)) ∧ ∀ σ : K →+* ℂ, Real.log ‖σ α‖ ≤ τ * (cost e t - t σ) + C := by
  first | exact @GlobalTheory.CovHt.exists_elt_balanced | exact GlobalTheory.CovHt.exists_elt_balanced | (intros; apply GlobalTheory.CovHt.exists_elt_balanced <;> assumption)
