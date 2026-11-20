import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AddFundamentalDomainMeasureEqOfCountable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.addFundamentalDomains_measure_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FAddFundamentalDomainMeasureEqOfCountable.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.addFundamentalDomain_measure_eq_of_countable : ∀ {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V) [μ.IsAddLeftInvariant] (L : Submodule ℤ V) [Countable L] (D D' : Set V), MeasurableSet D → MeasurableSet D' → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D) → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D') → μ D = μ D' := by
  first | exact @GlobalTheory.addFundamentalDomains_measure_eq | exact GlobalTheory.addFundamentalDomains_measure_eq | (intros; apply GlobalTheory.addFundamentalDomains_measure_eq <;> assumption)
