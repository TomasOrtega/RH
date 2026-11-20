import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QuotNorm

/- English proof (translation)
Establish `hinv : MeasurableInv H` using `⟨(measurable_subtype_coe.inv).subtype_mk⟩`. Use `⟨?_⟩` and prove the remaining obligations. Use extensionality with `s hs`. Rewrite using `[Measure.inv_apply, Measure.count_apply hs, Measure.count_apply hs.inv, ← Set.image_inv_eq_inv]`. Conclude with `congrArg ((↑) : ℕ∞ → ℝ≥0∞) (inv_injective.encard_image s)`.
-/
theorem count_isInvInvariant {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
    [MeasurableSingletonClass G] (H : Subgroup G) : (Measure.count : Measure H).IsInvInvariant := by
  have hinv : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  refine ⟨?_⟩
  ext s hs
  rw [Measure.inv_apply, Measure.count_apply hs, Measure.count_apply hs.inv, ← Set.image_inv_eq_inv]
  exact congrArg ((↑) : ℕ∞ → ℝ≥0∞) (inv_injective.encard_image s)

/- English proof (translation)
Introduce `G _ _ _ _ _ μ _ _ H _ F ρ hF hFH hρ`. Use `count_isInvInvariant H` as an intermediate fact. Conclude with `quotIntegral_eq (μG := μ) hF hFH hρ`.
-/
theorem qIndep : PositivityTheory.Rg.BcB.G8.QIndep := by
  intro G _ _ _ _ _ μ _ _ H _ F ρ hF hFH hρ
  have := count_isInvInvariant H
  exact quotIntegral_eq (μG := μ) hF hFH hρ

end GlobalTheory.CompanionTheory.QuotNorm
