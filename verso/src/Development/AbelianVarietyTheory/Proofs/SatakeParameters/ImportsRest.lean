import Mathlib

namespace GlobalTheory.ExistsSmulMem

/- English proof (translation)
Establish `hv : v ∈ Submodule.span E (↑Lb : Set (Fin N → E))` using `h ▸ Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `Lb.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `Lb.smul_mem _ hax`. Rewrite using `[mul_smul]`. Conclude with `Lb.smul_mem _ hby`. Consider the case `smul r x _ hx`.

Take `⟨a, ha, hax⟩` from `hx`. Take `⟨p, q, hq, rfl⟩` from `IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) r`. Establish `hq0 : q ≠ 0` using `nonZeroDivisors.ne_zero hq`. Establish `hq1 : algebraMap (NumberField.RingOfIntegers E) E q ≠ 0`. Introduce `h0`.

Conclude with `hq0 (FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers E) E (by rw [h0, map_zero]))`. Use `⟨q * a, mul_ne_zero hq0 ha, ?_⟩` and prove the remaining obligations. Establish `key : (q * a) • ((algebraMap (NumberField.RingOfIntegers E) E p / algebraMap (NumberField.RingOfIntegers E) E q) • x) = p • (a • x)`. Rewrite using `[← algebraMap_smul E (q * a), ← algebraMap_smul E p, ← algebraMap_smul E a, smul_smul, smul_smul, map_mul]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[key]`. Conclude with `Lb.smul_mem _ hax`.
-/
theorem exists_smul_mem {E : Type} [inst : Field E] [NumberField E] {N : ℕ}
    (Lb : Submodule (NumberField.RingOfIntegers E) (Fin N → E))
    (h : Submodule.span E (↑Lb : Set (Fin N → E)) = ⊤) (v : Fin N → E) :
    ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • v ∈ Lb := by
  have hv : v ∈ Submodule.span E (↑Lb : Set (Fin N → E)) := h ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Lb.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Lb.smul_mem _ hax
    · rw [mul_smul]; exact Lb.smul_mem _ hby
  | smul r x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) r
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (NumberField.RingOfIntegers E) E q ≠ 0 := by
      intro h0
      exact hq0 (FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers E) E
        (by rw [h0, map_zero]))
    refine ⟨q * a, mul_ne_zero hq0 ha, ?_⟩
    have key : (q * a) • ((algebraMap (NumberField.RingOfIntegers E) E p /
        algebraMap (NumberField.RingOfIntegers E) E q) • x) = p • (a • x) := by
      rw [← algebraMap_smul E (q * a), ← algebraMap_smul E p, ← algebraMap_smul E a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact Lb.smul_mem _ hax

end GlobalTheory.ExistsSmulMem
