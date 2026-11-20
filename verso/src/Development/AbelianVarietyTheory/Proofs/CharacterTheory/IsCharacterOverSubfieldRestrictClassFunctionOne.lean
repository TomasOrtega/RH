import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
namespace GlobalTheory

/- English proof (translation)
Introduce `K L _ _ _ G _ χ hχ`. Take `⟨n, ρ, hρ⟩` from `hχ`. Use `⟨?_, ?_, n, ?_, ?_⟩` and prove the remaining obligations. Introduce `H _ f`. Conclude with `⟨n, ρ.comp f, fun h => hρ (f h)⟩`.

Introduce `g x`. Rewrite using `[hρ, hρ]`. Establish `hc` using `ρ.char_conj g x⁻¹`. Rewrite `hc` using `[inv_inv]`. Rewrite using `[hc]`.

Rewrite using `[hρ, Representation.char_one]`. Simplify using the standard rewrite rules. Introduce and unpack `rfl`. Use function extensionality and compare the values at `g`. Establish `hz : ρ g = 0` using `LinearMap.ext fun v => Subsingleton.elim _ _`.

Rewrite using `[hρ, Pi.zero_apply, Representation.character, hz, map_zero, map_zero]`.
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
