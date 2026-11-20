import Mathlib

/- English proof (translation)
Introduce `R L _ _ φ h s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨1, by simp, by simp⟩`. Consider the case `insert z s _ ih`. Take `⟨b0, hb0, hs⟩` from `ih`.

Take `⟨a, b, hb, hz⟩` from `h z`. Use `⟨b0 * b, by rw [map_mul]; exact hb0.mul hb, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Break down `Finset.mem_insert.mp hw with rfl | hw` into its components or cases. Use `⟨a * b0, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul, ← hz]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨c, hc⟩` from `hs w hw`. Use `⟨c * b, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hc]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Reformulated.B.Yra3.main :
    ∀ {R L : Type} [inst : CommRing R] [inst_1 : CommRing L] (φ : R →+* L),
      (∀ (z : L), ∃ (a : R) (b : R), IsUnit ((φ : R → L) b) ∧ z * (φ : R → L) b = (φ : R → L) a) →
        ∀ (s : Finset L), ∃ (b : R), IsUnit ((φ : R → L) b) ∧ ∀ z ∈ s, z * (φ : R → L) b ∈ Set.range (⇑φ : R → L) := by
  intro R L _ _ φ h s
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert z s _ ih =>
    obtain ⟨b0, hb0, hs⟩ := ih
    obtain ⟨a, b, hb, hz⟩ := h z
    refine ⟨b0 * b, by rw [map_mul]; exact hb0.mul hb, ?_⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · refine ⟨a * b0, ?_⟩
      rw [map_mul, map_mul, ← hz]; ring
    · obtain ⟨c, hc⟩ := hs w hw
      refine ⟨c * b, ?_⟩
      rw [map_mul, map_mul, hc]; ring
