import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities.
-/
theorem isChar_restrict_conj_one : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (χ : G → L), IsChar K L χ → (∀ (H : Type) [Group H] (f : H →* G), IsChar K L (fun h => χ (f h))) ∧ (∀ g x : G, χ (x⁻¹ * g * x) = χ g) ∧ ∃ n : ℕ, χ 1 = (n : L) ∧ (n = 0 → χ = 0) := by
  intro K L _ _ _ G _ χ hχ
  obtain ⟨n, ρ, hρ⟩ := hχ
  refine ⟨?_, ?_, n, ?_, ?_⟩
  · intro H _ f
    exact ⟨n, ρ.comp f, fun h => hρ (f h)⟩
  · intro g x
    rw [hρ, hρ]
    have hc := ρ.char_conj g x⁻¹
    rw [inv_inv] at hc
    rw [hc]
  · rw [hρ, Representation.char_one]
    simp
  · rintro rfl
    funext g
    have hz : ρ g = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hρ, Pi.zero_apply, Representation.character, hz, map_zero, map_zero]
end GlobalTheory
