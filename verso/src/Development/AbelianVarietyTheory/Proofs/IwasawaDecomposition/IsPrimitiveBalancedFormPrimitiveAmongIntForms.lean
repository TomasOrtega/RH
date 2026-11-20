import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

/- English proof (translation)
Introduce `O _ bar X _ _ β hβ hp k β' hk`. Break down `Nat.eq_zero_or_pos k with rfl | hpos` into its components or cases. It suffices to derive a contradiction. Establish `h0 : (⟨β, hβ⟩ : balForms bar X) = 0` using `Subtype.ext (by simpa using hk.symm)`. Rewrite `hp` using `[h0]`.

Conclude with `not_isPrim_zero hp`. Establish `hk0 : (k : ℤ) ≠ 0` using `by exact_mod_cast hpos.ne'`. Establish `hval : ∀ y z, (k : ℤ) * β' y z = β y z`. Introduce `y z`. Rewrite using `[← hk]`.

Simplify using the standard rewrite rules. Establish `hb : β' ∈ balForms bar X`. Use `⟨fun y z => ?_, fun a y z => ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hk0` to reduce the goal to its premises. Rewrite using `[hval, hval]`.

Conclude with `hβ.1 y z`. Apply `mul_left_cancel₀ hk0` to reduce the goal to its premises. Rewrite using `[hval, hval]`. Conclude with `hβ.2 a y z`. Use `hp k ⟨β', hb⟩ (Subtype.ext ?_)` and prove the remaining obligations.

Simplify using `[← hk]`.
-/
theorem isPrim_eq_one_of_smul_eq : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (β : LinearMap.BilinForm ℤ X) (hβ : β ∈ balForms bar X), IsPrim bar (⟨β, hβ⟩ : balForms bar X) →
  ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1 := by
  intro O _ bar X _ _ β hβ hp k β' hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exfalso
    have h0 : (⟨β, hβ⟩ : balForms bar X) = 0 := Subtype.ext (by simpa using hk.symm)
    rw [h0] at hp
    exact not_isPrim_zero hp
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hval : ∀ y z, (k : ℤ) * β' y z = β y z := by
    intro y z
    rw [← hk]
    simp
  have hb : β' ∈ balForms bar X := by
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · apply mul_left_cancel₀ hk0
      rw [hval, hval]
      exact hβ.1 y z
    · apply mul_left_cancel₀ hk0
      rw [hval, hval]
      exact hβ.2 a y z
  refine hp k ⟨β', hb⟩ (Subtype.ext ?_)
  simp [← hk]

end GlobalTheory.PolFan
