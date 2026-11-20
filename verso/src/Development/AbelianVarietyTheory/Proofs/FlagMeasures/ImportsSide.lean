import Mathlib

namespace GlobalTheory.SaturatedSublattice

open NumberField

/- English proof (translation)
Introduce `E _ _ n Λ hspan v`. Establish `hv : v ∈ Submodule.span E (Λ : Set (Fin n → E))` using `by rw [hspan]; trivial`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨D1, hD1, h1⟩` from `hx`. Take `⟨D2, hD2, h2⟩` from `hy`. Use `⟨D1 * D2, mul_ne_zero hD1 hD2, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`.

Use `Λ.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `Λ.smul_mem D2 h1`. Rewrite using `[mul_smul]`. Conclude with `Λ.smul_mem D1 h2`.

Consider the case `smul a x _ hx`. Take `⟨D, hD, h⟩` from `hx`. Take `⟨⟨b, d⟩, hd⟩` from `IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a`. Simplify using `only at hd`. Use `⟨(d : RingOfIntegers E) * D, mul_ne_zero (nonZeroDivisors.coe_ne_zero d) hD, ?_⟩` and prove the remaining obligations.

Establish `key : ((d : RingOfIntegers E) * D) • (a • x) = b • (D • x)`. Rewrite using `[← algebraMap_smul E ((d : RingOfIntegers E) * D) (a • x), ← algebraMap_smul E b (D • x), ← algebraMap_smul E D x, smul_smul, smul_smul, map_mul, ← hd]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Conclude with `Λ.smul_mem b h`.
-/
theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.span E (↑Λ : Set (Fin n → E)) = ⊤ → ∀ (v : Fin n → E), ∃ (D : NumberField.RingOfIntegers E), D ≠ (0 : NumberField.RingOfIntegers E) ∧ D • v ∈ Λ := by
  intro E _ _ n Λ hspan v
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hspan]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨D1, hD1, h1⟩ := hx
    obtain ⟨D2, hD2, h2⟩ := hy
    refine ⟨D1 * D2, mul_ne_zero hD1 hD2, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem D2 h1
    · rw [mul_smul]; exact Λ.smul_mem D1 h2
  | smul a x _ hx =>
    obtain ⟨D, hD, h⟩ := hx
    obtain ⟨⟨b, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a
    simp only at hd
    refine ⟨(d : RingOfIntegers E) * D, mul_ne_zero (nonZeroDivisors.coe_ne_zero d) hD, ?_⟩
    have key : ((d : RingOfIntegers E) * D) • (a • x) = b • (D • x) := by
      rw [← algebraMap_smul E ((d : RingOfIntegers E) * D) (a • x), ← algebraMap_smul E b (D • x),
        ← algebraMap_smul E D x, smul_smul, smul_smul, map_mul, ← hd]
      congr 1
      ring
    rw [key]
    exact Λ.smul_mem b h

end GlobalTheory.SaturatedSublattice
