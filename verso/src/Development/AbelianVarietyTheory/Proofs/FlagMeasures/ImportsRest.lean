import Mathlib

namespace GlobalTheory.SmulMemSpan

/- English proof (translation)
Establish `hx : x ∈ Submodule.span K (L : Set V)` using `by rw [hL.span_eq_top]; trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨a, ha, hay⟩` from `hy`. Take `⟨b, hb, hbz⟩` from `hz`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `L.smul_mem b hay`. Rewrite using `[mul_smul]`. Conclude with `L.smul_mem a hbz`. Consider the case `smul c y _ hy`.

Take `⟨a, ha, hay⟩` from `hy`. Take `⟨n, d, hd, rfl⟩` from `IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) c`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Use `⟨d * a, mul_ne_zero hd0 ha, ?_⟩` and prove the remaining obligations. Establish `key : (d * a) • ((algebraMap (NumberField.RingOfIntegers K) K n / algebraMap (NumberField.RingOfIntegers K) K d) • y) = n • (a • y)`.

Establish `hdK : algebraMap (NumberField.RingOfIntegers K) K d ≠ 0`. Simplify using `using hd0`. Rewrite using `[← algebraMap_smul K (d * a), smul_smul, ← algebraMap_smul K n, ← algebraMap_smul K a, smul_smul, map_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[key]`. Conclude with `L.smul_mem n hay`.
-/
theorem exists_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (L : Submodule (NumberField.RingOfIntegers K) V) (hL : Submodule.IsLattice K L) (x : V) :
    ∃ (r : NumberField.RingOfIntegers K), r ≠ (0 : NumberField.RingOfIntegers K) ∧ r • x ∈ L := by
  have hx : x ∈ Submodule.span K (L : Set V) := by rw [hL.span_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem b hay
    · rw [mul_smul]; exact L.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    refine ⟨d * a, mul_ne_zero hd0 ha, ?_⟩
    have key : (d * a) • ((algebraMap (NumberField.RingOfIntegers K) K n /
        algebraMap (NumberField.RingOfIntegers K) K d) • y) = n • (a • y) := by
      have hdK : algebraMap (NumberField.RingOfIntegers K) K d ≠ 0 := by
        simpa using hd0
      rw [← algebraMap_smul K (d * a), smul_smul, ← algebraMap_smul K n, ← algebraMap_smul K a,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact L.smul_mem n hay

end GlobalTheory.SmulMemSpan
