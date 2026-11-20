import Mathlib

namespace GlobalTheory.ScalarMultipleInSpan

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact E.zero_mem⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hax⟩` from `hx`.

Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `E.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `E.smul_mem _ hax`. Rewrite using `[mul_smul]`. Conclude with `E.smul_mem _ hby`. Consider the case `smul c x _ hx`. Take `⟨a, ha, hax⟩` from `hx`.

Take `⟨p, q, hq, rfl⟩` from `IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) c`. Establish `hq0 : q ≠ 0` using `nonZeroDivisors.ne_zero hq`. Establish `hq1 : algebraMap (NumberField.RingOfIntegers K) K q ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (NumberField.RingOfIntegers K) K)).2 hq0`. Use `⟨a * q, mul_ne_zero ha hq0, ?_⟩` and prove the remaining obligations. Establish `h : (a * q) • ((algebraMap (NumberField.RingOfIntegers K) K p / algebraMap (NumberField.RingOfIntegers K) K q) • x) = p • (a • x)`.

Rewrite using `[← algebraMap_smul K (a * q), ← algebraMap_smul K p, ← algebraMap_smul K a, smul_smul, smul_smul, map_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h]`. Conclude with `E.smul_mem _ hax`.
-/
theorem exists_smul_mem_of_mem_span {K : Type} [Field K] [NumberField K] {r : ℕ}
    (E : Submodule (NumberField.RingOfIntegers K) (Fin r → K)) {v : Fin r → K}
    (hv : v ∈ Submodule.span K (↑E : Set (Fin r → K))) :
    ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • v ∈ E := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact E.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine E.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact E.smul_mem _ hax
    · rw [mul_smul]; exact E.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (NumberField.RingOfIntegers K) K q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (NumberField.RingOfIntegers K) K)).2 hq0
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have h : (a * q) • ((algebraMap (NumberField.RingOfIntegers K) K p /
        algebraMap (NumberField.RingOfIntegers K) K q) • x) = p • (a • x) := by
      rw [← algebraMap_smul K (a * q), ← algebraMap_smul K p, ← algebraMap_smul K a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [h]
    exact E.smul_mem _ hax

end GlobalTheory.ScalarMultipleInSpan
