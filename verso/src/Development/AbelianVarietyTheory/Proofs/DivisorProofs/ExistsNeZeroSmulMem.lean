import Mathlib

namespace GlobalTheory.NonzeroScalarMultipleMembership

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨a, ha, hay⟩` from `hy`.

Take `⟨b, hb, hbz⟩` from `hz`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `L.smul_mem _ hay`. Rewrite using `[mul_smul]`. Conclude with `L.smul_mem _ hbz`. Consider the case `smul c y _ hy`. Take `⟨a, ha, hay⟩` from `hy`.

Take `⟨p, q, hq, hpq⟩` from `IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) c`. Establish `hq0 : q ≠ 0` using `nonZeroDivisors.ne_zero hq`. Establish `hqK : algebraMap (NumberField.RingOfIntegers K) K q ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq`. Use `⟨a * q, mul_ne_zero ha hq0, ?_⟩` and prove the remaining obligations. Establish `h : (a * q) • (c • y) = p • (a • y)`.

Rewrite using `[← algebraMap_smul K (a * q), ← algebraMap_smul K p, ← algebraMap_smul K a, smul_smul, smul_smul, ← hpq, map_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h]`. Conclude with `L.smul_mem _ hay`.
-/
theorem exists_ne_zero_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {L : Submodule (NumberField.RingOfIntegers K) V} {x : V}
    (hx : x ∈ Submodule.span K (L : Set V)) :
    ∃ a : NumberField.RingOfIntegers K, a ≠ 0 ∧ a • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ hay
    · rw [mul_smul]; exact L.smul_mem _ hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap (NumberField.RingOfIntegers K) K q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have h : (a * q) • (c • y) = p • (a • y) := by
      rw [← algebraMap_smul K (a * q), ← algebraMap_smul K p, ← algebraMap_smul K a,
        smul_smul, smul_smul, ← hpq, map_mul]
      congr 1
      field_simp
    rw [h]
    exact L.smul_mem _ hay

end GlobalTheory.NonzeroScalarMultipleMembership
