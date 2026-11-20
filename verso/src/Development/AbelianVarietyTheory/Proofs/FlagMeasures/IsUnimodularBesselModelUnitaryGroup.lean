import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LintegralInvEqOfBiInvariantMatGroup

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

/- English proof (translation)
Introduce `k r μ hμ`. Take `⟨hG, h⟩` from `GlobalTheory.unitaryGroup_matGroup_unimodular k r`. Take `⟨hM, hR⟩` from `h μ hμ`. Use `⟨fun s hs => hR s hs, ?_⟩` and prove the remaining obligations. Use `Measure.ext_of_lintegral _ fun f hf => ?_` and prove the remaining obligations.

Rewrite using `[lintegral_map hf measurable_invM]`. Conclude with `GlobalTheory.HaarInversion.lintegral_inv_eq _ (GG k r) μ hG hM hR f hf`.
-/
theorem isUnimod_GG : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → IsUnimod (GG k r) μ := by
  intro k r μ hμ
  obtain ⟨hG, h⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  obtain ⟨hM, hR⟩ := h μ hμ
  refine ⟨fun s hs => hR s hs, ?_⟩
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf measurable_invM]
  exact GlobalTheory.HaarInversion.lintegral_inv_eq _ (GG k r) μ hG hM hR f hf

end GlobalTheory.SgInf

/- English proof (translation)
The claim follows from `GlobalTheory.SgInf.isUnimod_GG`.
-/
example : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → IsUnimod (GG k r) μ := GlobalTheory.SgInf.isUnimod_GG
