import Mathlib

namespace GlobalTheory.DeterminantSimpLemma

open NumberField

/- English proof (translation)
Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨d₁, hd₁, h₁⟩` from `hy`. Take `⟨d₂, hd₂, h₂⟩` from `hz`. Use `⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `M.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `M.smul_mem _ h₁`. Rewrite using `[mul_smul]`. Conclude with `M.smul_mem _ h₂`. Consider the case `smul c y _ hy`.

Take `⟨d, hd, h⟩` from `hy`. Take `⟨a, b, hb, hab⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) c`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hbK : (algebraMap (𝓞 K) K b) ≠ 0`. Simplify using `using hb0`.

Use `⟨b * d, mul_ne_zero hb0 hd, ?_⟩` and prove the remaining obligations. Establish `key : (b * d) • (c • y) = a • (d • y)`. Rewrite using `[← algebraMap_smul K (b * d), ← algebraMap_smul K a, ← algebraMap_smul K d, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[← hab, map_mul]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[key]`. Conclude with `M.smul_mem _ h`.
-/
theorem main {K : Type} [inst : Field K] [NumberField K] {n : ℕ}
    {M : Submodule (NumberField.RingOfIntegers K) (Fin n → K)} {x : Fin n → K} :
    x ∈ Submodule.span K (↑M : Set (Fin n → K)) →
      ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • x ∈ M := by
  intro hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h₁
    · rw [mul_smul]; exact M.smul_mem _ h₂
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : (algebraMap (𝓞 K) K b) ≠ 0 := by
      simpa using hb0
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have key : (b * d) • (c • y) = a • (d • y) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K a, ← algebraMap_smul K d,
        smul_smul, smul_smul]
      congr 1
      rw [← hab, map_mul]
      field_simp
    rw [key]
    exact M.smul_mem _ h

end GlobalTheory.DeterminantSimpLemma
