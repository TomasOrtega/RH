import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUntiltExtensionFinsetSumSubLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNormUntiltExtensionFinsetSumSubLe.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.norm_untilt_extension_finset_sum_sub_le : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (α : Type) (s : Finset α) (z : α → F) (R : ℝ), 0 ≤ R → (∀ a ∈ s, ‖z a‖ ≤ R) →
      ‖tsh (∑ a ∈ s, z a) - ∑ a ∈ s, tsh (z a)‖ ≤ ‖(l : ℂ_[l])‖ * R := by
  first | exact @GlobalTheory.untilt_ext_sum_sub_le | exact GlobalTheory.untilt_ext_sum_sub_le | (intros; apply GlobalTheory.untilt_ext_sum_sub_le <;> assumption)
