import Mathlib

namespace GlobalTheory.FiniteSumFlagMeasures

open NumberField

/- English proof (translation)
Establish `hv : v ∈ Submodule.span K (↑B : Set (Fin b → K))` using `by rw [hB]; trivial`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨d₁, hd₁, h₁⟩` from `hx`. Take `⟨d₂, hd₂, h₂⟩` from `hy`. Use `⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `B.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `B.smul_mem _ h₁`. Rewrite using `[mul_smul]`. Conclude with `B.smul_mem _ h₂`. Consider the case `smul c x _ hx`.

Take `⟨d, hd, h⟩` from `hx`. Take `⟨⟨n, m⟩, hnm⟩` from `IsLocalization.surj (nonZeroDivisors (𝓞 K)) c`. Simplify using `only at hnm`. Use `⟨(m : 𝓞 K) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero m) hd, ?_⟩` and prove the remaining obligations. Establish `key : ((m : 𝓞 K) * d) • (c • x) = n • (d • x)`.

Rewrite using `[← algebraMap_smul K ((m : 𝓞 K) * d), ← algebraMap_smul K n, ← algebraMap_smul K d, smul_smul, smul_smul, map_mul, ← hnm]`. Put the polynomial expressions in normal form. Rewrite using `[key]`. Conclude with `B.smul_mem _ h`.
-/
theorem main {K : Type} [Field K] [NumberField K] {b : ℕ}
    (B : Submodule (NumberField.RingOfIntegers K) (Fin b → K))
    (hB : Submodule.span K (↑B : Set (Fin b → K)) = ⊤) (v : Fin b → K) :
    ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • v ∈ B := by
  have hv : v ∈ Submodule.span K (↑B : Set (Fin b → K)) := by rw [hB]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine B.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact B.smul_mem _ h₁
    · rw [mul_smul]; exact B.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨n, m⟩, hnm⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) c
    simp only at hnm
    refine ⟨(m : 𝓞 K) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero m) hd, ?_⟩
    have key : ((m : 𝓞 K) * d) • (c • x) = n • (d • x) := by
      rw [← algebraMap_smul K ((m : 𝓞 K) * d), ← algebraMap_smul K n, ← algebraMap_smul K d,
        smul_smul, smul_smul, map_mul, ← hnm]
      ring_nf
    rw [key]; exact B.smul_mem _ h

end GlobalTheory.FiniteSumFlagMeasures
