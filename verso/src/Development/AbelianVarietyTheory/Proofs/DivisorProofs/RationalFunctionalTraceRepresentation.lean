import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ g hg`. Use `choose f hf using hg`. Set `g' : E →ₗ[ℚ] ℚ` to `{ toFun := f map_add' := by`. Introduce `x y`. Apply `(Rat.cast_injective (α := ℝ))` to reduce the goal to its premises.

Rewrite using `[Rat.cast_add, ← hf, ← hf, ← hf, map_add]`. Use the proof step `map_smul' := by`. Introduce `c x`. Apply `(Rat.cast_injective (α := ℝ))` to reduce the goal to its premises. Rewrite using `[smul_eq_mul, RingHom.id_apply, Rat.cast_mul, ← hf, ← hf, map_smul, Rat.smul_def] }`.

Establish `hB` using `traceForm_nondegenerate ℚ E`. Use `⟨(LinearMap.BilinForm.toDual _ hB).symm g', fun z => ?_⟩` and prove the remaining obligations. Establish `h1 : (LinearMap.BilinForm.toDual _ hB ((LinearMap.BilinForm.toDual _ hB).symm g')) z = g' z`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Rewrite `h1` using `[LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply]`.

Rewrite using `[h1]`. Conclude with `hf z`.
-/
theorem linearMap_rat_valued_eq_trace : ∀ (E : Type) [Field E] [NumberField E] (g : E →ₗ[ℚ] ℝ), (∀ z, ∃ q : ℚ, g z = q) →
    ∃ mu : E, ∀ z, g z = ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) := by
  intro E _ _ g hg
  choose f hf using hg
  let g' : E →ₗ[ℚ] ℚ :=
    { toFun := f
      map_add' := by
        intro x y
        apply (Rat.cast_injective (α := ℝ))
        rw [Rat.cast_add, ← hf, ← hf, ← hf, map_add]
      map_smul' := by
        intro c x
        apply (Rat.cast_injective (α := ℝ))
        rw [smul_eq_mul, RingHom.id_apply, Rat.cast_mul, ← hf, ← hf, map_smul, Rat.smul_def] }
  have hB := traceForm_nondegenerate ℚ E
  refine ⟨(LinearMap.BilinForm.toDual _ hB).symm g', fun z => ?_⟩
  have h1 : (LinearMap.BilinForm.toDual _ hB ((LinearMap.BilinForm.toDual _ hB).symm g')) z = g' z := by
    rw [LinearEquiv.apply_symm_apply]
  rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at h1
  rw [h1]
  exact hf z

end GlobalTheory
