import Mathlib

namespace GlobalTheory.IntegralBoundFlagMeasures

open NumberField

/- English proof (translation)
Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x z _ _ hx hz`.

Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hbz⟩` from `hz`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Establish `h1 : (a * b) • x = b • (a • x)` using `by rw [mul_comm, mul_smul]`. Establish `h2 : (a * b) • z = a • (b • z)` using `by rw [mul_smul]`.

Rewrite using `[smul_add, h1, h2]`. Conclude with `Λ.add_mem (Λ.smul_mem _ hax) (Λ.smul_mem _ hbz)`. Consider the case `smul e x _ hx`. Take `⟨c, hc, hcx⟩` from `hx`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors (𝓞 E)) e`.

Simplify using `only at hab`. Establish `hb : (b : 𝓞 E) ≠ 0` using `nonZeroDivisors.ne_zero b.2`. Use `⟨(b : 𝓞 E) * c, mul_ne_zero hb hc, ?_⟩` and prove the remaining obligations. Establish `key : (b : 𝓞 E) • (e • x) = a • x`. Rewrite using `[← algebraMap_smul E (b : 𝓞 E) (e • x), smul_smul, mul_comm, hab, algebraMap_smul]`.

Establish `: ((b : 𝓞 E) * c) • (e • x) = a • (c • x)`. Rewrite using `[mul_comm, mul_smul, key, smul_comm]`. Rewrite using `[this]`. Conclude with `Λ.smul_mem _ hcx`.
-/
theorem main {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) :
    ∀ y ∈ Submodule.span E (↑Λ : Set (Fin n → E)),
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • y ∈ Λ := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • z = a • (b • z) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact Λ.add_mem (Λ.smul_mem _ hax) (Λ.smul_mem _ hbz)
  | smul e x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) e
    simp only at hab
    have hb : (b : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero b.2
    refine ⟨(b : 𝓞 E) * c, mul_ne_zero hb hc, ?_⟩
    have key : (b : 𝓞 E) • (e • x) = a • x := by
      rw [← algebraMap_smul E (b : 𝓞 E) (e • x), smul_smul, mul_comm, hab, algebraMap_smul]
    have : ((b : 𝓞 E) * c) • (e • x) = a • (c • x) := by
      rw [mul_comm, mul_smul, key, smul_comm]
    rw [this]
    exact Λ.smul_mem _ hcx

end GlobalTheory.IntegralBoundFlagMeasures
