import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.ValSurjective

open NumberField IsDedekindDomain Uniformity

namespace PI.LocalEndW

/- English proof (translation)
Establish `hb` using `Valued.hasBasis_uniformity (v.adicCompletion F) _`. Establish `hτ' : ∀ y, Valued.v.restrict (τ y) = Valued.v.restrict y` using `fun y => le_antisymm (not_lt.1 fun h => lt_irrefl (Valued.v y) (by rw [Valuation.restrict_lt_iff, hτ] at h; exact h)) (not_lt.1 fun h => lt_irrefl (Valued.v y) (by rw [Valuation.restrict_lt_iff, hτ] at h; exact h))`. Use `⟨(hb.comap _).ext hb (fun γ _ => ⟨γ, trivial, ?_⟩) (fun γ _ => ⟨γ, trivial, ?_⟩)⟩` and prove the remaining obligations. Introduce `p hp`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq] at hp ⊢`.

Rewrite using `[← map_sub, hτ']`. Conclude with `hp`. Introduce `p hp`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq] at hp ⊢`. Rewrite `hp` using `[← map_sub, hτ']`. Then use the resulting hypothesis.
-/
theorem isUniformInducing_of_val {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (τ : v.adicCompletion F →+* v.adicCompletion F) (hτ : ∀ x, Valued.v (τ x) = Valued.v x) :
    IsUniformInducing τ := by
  have hb := Valued.hasBasis_uniformity (v.adicCompletion F) _
  have hτ' : ∀ y, Valued.v.restrict (τ y) = Valued.v.restrict y := fun y =>
    le_antisymm
      (not_lt.1 fun h => lt_irrefl (Valued.v y) (by rw [Valuation.restrict_lt_iff, hτ] at h; exact h))
      (not_lt.1 fun h => lt_irrefl (Valued.v y) (by rw [Valuation.restrict_lt_iff, hτ] at h; exact h))
  refine ⟨(hb.comap _).ext hb (fun γ _ => ⟨γ, trivial, ?_⟩) (fun γ _ => ⟨γ, trivial, ?_⟩)⟩
  · intro p hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hp ⊢
    rw [← map_sub, hτ']
    exact hp
  · intro p hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hp ⊢
    rwa [← map_sub, hτ'] at hp

/- English proof (translation)
Introduce `_ _ _ _ τ hτ` and use `(isUniformInducing_of_val τ hτ).uniformContinuous.continuous`.
-/
theorem valContinuous : ValContinuous := fun _ _ _ _ τ hτ => (isUniformInducing_of_val τ hτ).uniformContinuous.continuous

end PI.LocalEndW
