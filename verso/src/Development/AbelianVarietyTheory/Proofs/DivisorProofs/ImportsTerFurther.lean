import Mathlib

open NumberField

namespace GlobalTheory.SimplifiedNormIdentities

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨s, hs, hsy⟩` from `hy`. Take `⟨t, ht, htz⟩` from `hz`. Use `⟨s * t, mul_ne_zero hs ht, ?_⟩` and prove the remaining obligations. Establish `h1 : (s * t) • y = t • (s • y)` using `by rw [mul_comm, mul_smul]`. Establish `h2 : (s * t) • z = s • (t • z)` using `by rw [mul_smul]`.

Rewrite using `[smul_add, h1, h2]`. Conclude with `B.add_mem (B.smul_mem t hsy) (B.smul_mem s htz)`. Consider the case `smul c y _ hy`. Take `⟨s, hs, hsy⟩` from `hy`. Take `⟨a, d, hd, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) c`.

Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Establish `hdK : algebraMap (𝓞 K) K d ≠ 0`. Simplify using `using hd0`. Use `⟨d * s, mul_ne_zero hd0 hs, ?_⟩` and prove the remaining obligations. Establish `key : (d * s) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K d) • y) = a • (s • y)`.

Rewrite using `[← algebraMap_smul K (d * s), ← algebraMap_smul K a, ← algebraMap_smul K s, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[map_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key]`.

Conclude with `B.smul_mem a hsy`.
-/
theorem main {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (B : Submodule (𝓞 K) V) :
    ∀ x ∈ Submodule.span K (↑B : Set V), ∃ s : 𝓞 K, s ≠ 0 ∧ s • x ∈ B := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have h1 : (s * t) • y = t • (s • y) := by rw [mul_comm, mul_smul]
    have h2 : (s * t) • z = s • (t • z) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact B.add_mem (B.smul_mem t hsy) (B.smul_mem s htz)
  | smul c y _ hy =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
      simpa using hd0
    refine ⟨d * s, mul_ne_zero hd0 hs, ?_⟩
    have key : (d * s) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K d) • y) = a • (s • y) := by
      rw [← algebraMap_smul K (d * s), ← algebraMap_smul K a, ← algebraMap_smul K s,
        smul_smul, smul_smul]
      congr 1
      rw [map_mul]
      field_simp
    rw [key]
    exact B.smul_mem a hsy

end GlobalTheory.SimplifiedNormIdentities
