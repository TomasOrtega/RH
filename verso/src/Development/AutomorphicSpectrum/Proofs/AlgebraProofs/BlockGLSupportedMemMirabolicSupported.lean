import Mathlib
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Apply `((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).injective` to reduce the goal to its premises. Use extensionality with `a`. Rewrite using `[LinearMap.BilinForm.toDual_def, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply, Algebra.traceForm_apply, mul_comm b, mul_comm c]`. Conclude with `h a`.
-/
private theorem eq_of_forall_trace_mul_eq_trace_mul {E : Type} [Field E] [NumberField E] {b c : E}
    (h : ∀ a : E, Algebra.trace ℚ E (a * b) = Algebra.trace ℚ E (a * c)) : b = c := by
  apply ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).injective
  ext a
  rw [LinearMap.BilinForm.toDual_def, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply,
    Algebra.traceForm_apply, mul_comm b, mul_comm c]
  exact h a

/- English proof (translation)
Introduce `E _ _ _ V _ _ _ _ B hB`. Choose the witnesses or unpack the hypotheses as in `⟨h, htr⟩ : ∃ h : V → V → E, ∀ x y (a : E), Algebra.trace ℚ E (a * h x y) = B (a • x) y := by`. Use `⟨fun x y => ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm { toFun := fun a => B (a • x) y map_add' := fun a b => by simp only [add_smul, map_add, LinearMap.add_apply] map_smul' := fun q a => by` and prove the remaining obligations. Simplify using `only [smul_assoc, map_smul, LinearMap.smul_apply, RingHom.id_apply] }, ?_⟩`. Introduce `x y a`.

Simplify using `only`. Rewrite using `[mul_comm, ← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]`. Both sides reduce to the same expression. Use `⟨h, ⟨htr, ?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x x' y`.

Apply `eq_of_forall_trace_mul_eq_trace_mul` to reduce the goal to its premises. Introduce `a`. Rewrite using `[mul_add, map_add, htr, htr, htr, smul_add, map_add, LinearMap.add_apply]`. Introduce `x y y'`. Apply `eq_of_forall_trace_mul_eq_trace_mul` to reduce the goal to its premises.

Introduce `a`. Rewrite using `[mul_add, map_add, htr, htr, htr, map_add]`. Introduce `b x y`. Apply `eq_of_forall_trace_mul_eq_trace_mul` to reduce the goal to its premises. Introduce `a`.

Rewrite using `[htr, ← mul_assoc, htr, mul_smul]`. Introduce `b x y`. Apply `eq_of_forall_trace_mul_eq_trace_mul` to reduce the goal to its premises. Introduce `a`. Rewrite using `[htr, ← mul_assoc, htr, mul_comm a, mul_smul, hB (IsCMField.complexConj E b) (a • x) y, IsCMField.complexConj_apply_apply]`.

Introduce and unpack `h' ⟨htr', -⟩`. Use function extensionality and compare the values at `x y`. Apply `eq_of_forall_trace_mul_eq_trace_mul` to reduce the goal to its premises. Introduce `a`. Rewrite using `[htr', htr]`.
-/
theorem existsUnique_sesq_of_trace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (V : Type) [AddCommGroup V] [Module E V] [Module ℚ V] [IsScalarTower ℚ E V] (B : LinearMap.BilinForm ℚ V), (∀ (a : E) x y, B (a • x) y = B x (IsCMField.complexConj E a • y)) → ∃! h : V → V → E, (∀ x y (a : E), Algebra.trace ℚ E (a * h x y) = B (a • x) y) ∧ (∀ x x' y, h (x + x') y = h x y + h x' y) ∧ (∀ x y y', h x (y + y') = h x y + h x y') ∧ (∀ (a : E) x y, h (a • x) y = a * h x y) ∧ (∀ (a : E) x y, h x (a • y) = IsCMField.complexConj E a * h x y) := by
  intro E _ _ _ V _ _ _ _ B hB
  obtain ⟨h, htr⟩ : ∃ h : V → V → E,
      ∀ x y (a : E), Algebra.trace ℚ E (a * h x y) = B (a • x) y := by
    refine ⟨fun x y => ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm
      { toFun := fun a => B (a • x) y
        map_add' := fun a b => by simp only [add_smul, map_add, LinearMap.add_apply]
        map_smul' := fun q a => by
          simp only [smul_assoc, map_smul, LinearMap.smul_apply, RingHom.id_apply] }, ?_⟩
    intro x y a
    dsimp only
    rw [mul_comm, ← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
    rfl
  refine ⟨h, ⟨htr, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x x' y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [mul_add, map_add, htr, htr, htr, smul_add, map_add, LinearMap.add_apply]
  · intro x y y'
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [mul_add, map_add, htr, htr, htr, map_add]
  · intro b x y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [htr, ← mul_assoc, htr, mul_smul]
  · intro b x y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [htr, ← mul_assoc, htr, mul_comm a, mul_smul, hB (IsCMField.complexConj E b) (a • x) y,
      IsCMField.complexConj_apply_apply]
  · rintro h' ⟨htr', -⟩
    funext x y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [htr', htr]

end GlobalTheory.CompanionTheory.Ar.Flat
