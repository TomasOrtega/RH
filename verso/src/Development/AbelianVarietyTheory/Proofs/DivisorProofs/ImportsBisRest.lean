import Mathlib

namespace GlobalTheory.HermitianEigenvalueInequality

/- English proof (translation)
Introduce `E _ _ n L x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨d₁, hd₁, h₁⟩` from `hy`. Take `⟨d₂, hd₂, h₂⟩` from `hz`. Use `⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩` and prove the remaining obligations. Establish `e : (d₁ * d₂) • (y + z) = d₂ • (d₁ • y) + d₁ • (d₂ • z)`. Rewrite using `[smul_add, mul_comm, mul_smul, mul_comm, mul_smul]`.

Rewrite using `[e]`. Conclude with `L.add_mem (L.smul_mem _ h₁) (L.smul_mem _ h₂)`. Consider the case `smul c y _ hy`. Take `⟨d, hd, h⟩` from `hy`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c`.

Use `⟨(b : NumberField.RingOfIntegers E) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero b) hd, ?_⟩` and prove the remaining obligations. Establish `e : ((b : NumberField.RingOfIntegers E) * d) • (c • y) = a • (d • y)`. Simplify using `only at hab`. Rewrite using `[← algebraMap_smul E ((b : NumberField.RingOfIntegers E) * d), ← algebraMap_smul E a, ← algebraMap_smul E d, smul_smul, smul_smul, map_mul, ]`. Use `congr 1`.

Rewrite using `[← hab]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `L.smul_mem _ h`.
-/
theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), ∀ x ∈ Submodule.span E (↑L : Set (Fin n → E)), ∃ (d : NumberField.RingOfIntegers E), d ≠ (0 : NumberField.RingOfIntegers E) ∧ d • x ∈ L := by
  intro E _ _ n L x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e : (d₁ * d₂) • (y + z) = d₂ • (d₁ • y) + d₁ • (d₂ • z) := by
      rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem _ h₁) (L.smul_mem _ h₂)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c
    refine ⟨(b : NumberField.RingOfIntegers E) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero b) hd, ?_⟩
    have e : ((b : NumberField.RingOfIntegers E) * d) • (c • y) = a • (d • y) := by
      simp only at hab
      rw [← algebraMap_smul E ((b : NumberField.RingOfIntegers E) * d), ← algebraMap_smul E a,
        ← algebraMap_smul E d, smul_smul, smul_smul, map_mul, ]
      congr 1
      rw [← hab]
      ring
    rw [e]
    exact L.smul_mem _ h

end GlobalTheory.HermitianEigenvalueInequality
