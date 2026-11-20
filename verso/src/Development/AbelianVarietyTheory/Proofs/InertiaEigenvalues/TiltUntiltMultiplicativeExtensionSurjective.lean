import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLaws
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.TshOnto

/- English proof (translation)
Introduce `l _ F _ ι tsh _hn hsh _ t`. Take `⟨-, -, -, -, -, honto, -, -⟩` from `GlobalTheory.PSer.Laws.sh_laws l`. Distinguish the cases in `ht : ‖t‖ ≤ 1`. Take `⟨x, hx⟩` from `honto t ht`. Conclude with `⟨ι x, by rw [hsh, hx]⟩`.

Use `push_neg at ht`. Establish `hinv : ‖t⁻¹‖ ≤ 1`. Rewrite using `[norm_inv]`. Conclude with `inv_le_one_of_one_le₀ ht.le`. Take `⟨x, hx⟩` from `honto t⁻¹ hinv`.

Use `⟨(ι x)⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv₀, hsh, hx, inv_inv]`.
-/
theorem tsh_surjective : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ t : ℂ_[l], ∃ z : F, tsh z = t := by
  intro l _ F _ ι tsh _hn hsh _ t
  obtain ⟨-, -, -, -, -, honto, -, -⟩ := GlobalTheory.PSer.Laws.sh_laws l
  by_cases ht : ‖t‖ ≤ 1
  · obtain ⟨x, hx⟩ := honto t ht
    exact ⟨ι x, by rw [hsh, hx]⟩
  · push_neg at ht
    have hinv : ‖t⁻¹‖ ≤ 1 := by
      rw [norm_inv]; exact inv_le_one_of_one_le₀ ht.le
    obtain ⟨x, hx⟩ := honto t⁻¹ hinv
    refine ⟨(ι x)⁻¹, ?_⟩
    rw [map_inv₀, hsh, hx, inv_inv]

end GlobalTheory.PSer.TshOnto
