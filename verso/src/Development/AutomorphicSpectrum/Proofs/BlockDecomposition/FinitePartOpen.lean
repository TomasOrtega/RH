import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FinOpenGram

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ n μ ν m hμ hν hm f hf hfin U hU hne`. Establish `: BorelSpace (HermR (Ainf F) σ n)` using `⟨rfl⟩`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hpos : ν U ≠ 0` using `(hU.measure_pos ν hne).ne'`.

Establish `h2` using `hm`. Unfold `GlobalTheory.CompanionTheory.SW.IsGramFib Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h2`. Establish `hfib` using `h2.2.1 f hf`. Establish `hle : (⊤ : ℝ≥0∞) * ν U ≤ ∫⁻ S, ∫⁻ X, f X ∂(m S) ∂ν`. Rewrite using `[← lintegral_indicator_const hU.measurableSet]`.

Use `lintegral_mono fun S => ?_` and prove the remaining obligations. Distinguish the cases in `hS : S ∈ U`. Rewrite using `[Set.indicator_of_mem hS, hcon S hS]`. Rewrite using `[Set.indicator_of_notMem hS]`. Conclude with `bot_le`.

Rewrite `hle` using `[ENNReal.top_mul hpos, top_le_iff, ← hfib]`. Conclude with `hfin (top_le_iff.1 (hle ▸ setLIntegral_le_lintegral _ _))`.
-/
theorem finOpen : PositivityTheory.PfSWUS.SchInf.FinOpen := by
  intro F E _ _ _ _ _ σ hCM M J hJ n μ ν m hμ hν hm f hf hfin U hU hne
  have : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  by_contra hcon
  push Not at hcon
  have hpos : ν U ≠ 0 := (hU.measure_pos ν hne).ne'
  have h2 := hm
  unfold GlobalTheory.CompanionTheory.SW.IsGramFib Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h2
  have hfib := h2.2.1 f hf
  have hle : (⊤ : ℝ≥0∞) * ν U ≤ ∫⁻ S, ∫⁻ X, f X ∂(m S) ∂ν := by
    rw [← lintegral_indicator_const hU.measurableSet]
    refine lintegral_mono fun S => ?_
    by_cases hS : S ∈ U
    · rw [Set.indicator_of_mem hS, hcon S hS]
    · rw [Set.indicator_of_notMem hS]
      exact bot_le
  rw [ENNReal.top_mul hpos, top_le_iff, ← hfib] at hle
  exact hfin (top_le_iff.1 (hle ▸ setLIntegral_le_lintegral _ _))

end GlobalTheory.CompanionTheory.SW.FinOpenGram
end
