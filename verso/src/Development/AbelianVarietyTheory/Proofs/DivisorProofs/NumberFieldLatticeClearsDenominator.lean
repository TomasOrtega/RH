import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
open NumberField ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory

/- English proof (translation)
Establish `hx : x ∈ Submodule.span K (L : Set (Fin m → K))` using `hL ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨d₁, hd₁, h₁⟩` from `hy`. Take `⟨d₂, hd₂, h₂⟩` from `hz`. Use `⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩` and prove the remaining obligations. Establish `e1 : (d₁ * d₂) • y = d₂ • (d₁ • y)` using `by rw [mul_comm, mul_smul]`. Establish `e2 : (d₁ * d₂) • z = d₁ • (d₂ • z)` using `by rw [mul_smul]`.

Rewrite using `[smul_add, e1, e2]`. Conclude with `L.add_mem (L.smul_mem _ h₁) (L.smul_mem _ h₂)`. Consider the case `smul c y _ hy`. Take `⟨d, hd, h⟩` from `hy`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) c`.

Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hbK : (algebraMap (𝓞 K) K b) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`. Use `⟨b * d, mul_ne_zero hb0 hd, ?_⟩` and prove the remaining obligations. Establish `key : (b * d) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) • y) = a • (d • y)`. Rewrite using `[← algebraMap_smul K (b * d), ← algebraMap_smul K a, ← algebraMap_smul K d, smul_smul, smul_smul]`.

Use `congr 1`. Rewrite using `[map_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key]`. Conclude with `L.smul_mem _ h`.
-/
theorem exists_ne_zero_smul_mem_of_kspan_eq_top {K : Type} [Field K] [NumberField K] {m : ℕ}
    (L : Submodule (𝓞 K) (Fin m → K)) (hL : Submodule.span K (L : Set (Fin m → K)) = ⊤)
    (x : Fin m → K) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ L := by
  have hx : x ∈ Submodule.span K (L : Set (Fin m → K)) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e1 : (d₁ * d₂) • y = d₂ • (d₁ • y) := by rw [mul_comm, mul_smul]
    have e2 : (d₁ * d₂) • z = d₁ • (d₂ • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact L.add_mem (L.smul_mem _ h₁) (L.smul_mem _ h₂)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : (algebraMap (𝓞 K) K b) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have key : (b * d) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) • y) = a • (d • y) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K a, ← algebraMap_smul K d,
        smul_smul, smul_smul]
      congr 1
      rw [map_mul]
      field_simp
    rw [key]
    exact L.smul_mem _ h

end GlobalTheory
