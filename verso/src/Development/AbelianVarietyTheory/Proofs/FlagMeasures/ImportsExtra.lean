import Mathlib

namespace GlobalTheory.ClearingDenominatorsInOrder

/- English proof (translation)
Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨c1, hc1, h1⟩` from `hx`. Take `⟨c2, hc2, h2⟩` from `hy`. Use `⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Apply `L.add_mem` to reduce the goal to its premises.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `L.smul_mem c2 h1`. Rewrite using `[mul_smul]`. Conclude with `L.smul_mem c1 h2`. Consider the case `smul a x _ hx`.

Take `⟨c, hc, h⟩` from `hx`. Take `⟨⟨n, d⟩, hnd⟩` from `IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) a`. Simplify using `only at hnd`. Establish `hd : (d : NumberField.RingOfIntegers E) ≠ 0` using `nonZeroDivisors.coe_ne_zero d`. Use `⟨c * d, mul_ne_zero hc hd, ?_⟩` and prove the remaining obligations.

Establish `key : (d : NumberField.RingOfIntegers E) • (a • x) = n • x`. Rewrite using `[← algebraMap_smul E (d : NumberField.RingOfIntegers E), smul_smul, mul_comm, hnd, algebraMap_smul]`. Rewrite using `[mul_smul, key, smul_comm]`. Conclude with `L.smul_mem n h`.
-/
theorem main {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    [Module (NumberField.RingOfIntegers E) W]
    [IsScalarTower (NumberField.RingOfIntegers E) E W]
    (L : Submodule (NumberField.RingOfIntegers E) W) :
    ∀ v ∈ Submodule.span E (↑L : Set W),
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • v ∈ L := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c1, hc1, h1⟩ := hx
    obtain ⟨c2, hc2, h2⟩ := hy
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
    rw [smul_add]
    apply L.add_mem
    · rw [mul_comm, mul_smul]; exact L.smul_mem c2 h1
    · rw [mul_smul]; exact L.smul_mem c1 h2
  | smul a x _ hx =>
    obtain ⟨c, hc, h⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) a
    simp only at hnd
    have hd : (d : NumberField.RingOfIntegers E) ≠ 0 := nonZeroDivisors.coe_ne_zero d
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    have key : (d : NumberField.RingOfIntegers E) • (a • x) = n • x := by
      rw [← algebraMap_smul E (d : NumberField.RingOfIntegers E), smul_smul, mul_comm, hnd,
        algebraMap_smul]
    rw [mul_smul, key, smul_comm]
    exact L.smul_mem n h

end GlobalTheory.ClearingDenominatorsInOrder
