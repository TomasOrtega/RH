import Mathlib

namespace Bl.general_b_fact_left''''''''

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ L v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨d1, hd1, h1⟩` from `hx`. Take `⟨d2, hd2, h2⟩` from `hy`. Use `⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `L.smul_mem d2 h1`. Rewrite using `[mul_smul]`. Conclude with `L.smul_mem d1 h2`. Consider the case `smul a x _ hx`.

Take `⟨d, hd, h⟩` from `hx`. Take `⟨⟨n, m⟩, hm⟩` from `IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a`. Use `⟨(m : NumberField.RingOfIntegers K) * d, mul_ne_zero (nonZeroDivisors.ne_zero m.2) hd, ?_⟩` and prove the remaining obligations. Establish `key : ((m : NumberField.RingOfIntegers K) * d) • (a • x) = n • (d • x)`. Rewrite using `[← algebraMap_smul K ((m : NumberField.RingOfIntegers K) * d) (a • x), ← algebraMap_smul K n (d • x), ← algebraMap_smul K d x, smul_smul, smul_smul, map_mul]`.

Use `congr 1`. Rewrite using `[← hm]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `L.smul_mem n h`.
-/
theorem goal1 :
  ∀ {K V : Type} [inst : Field.{0} K] [NumberField.{0} K] [inst_2 : AddCommGroup.{0} V] [inst_3 : Module.{0, 0} K V]
  [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} K) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K V]
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) V) (v : V),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} L)) v →
    Exists.{1} fun (d : NumberField.RingOfIntegers.{0} K) ↦
      And (Ne.{1} d 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} d v)) := by
  intro K V _ _ _ _ _ _ L v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d1, hd1, h1⟩ := hx
    obtain ⟨d2, hd2, h2⟩ := hy
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem d2 h1
    · rw [mul_smul]
      exact L.smul_mem d1 h2
  | smul a x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨n, m⟩, hm⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a
    refine ⟨(m : NumberField.RingOfIntegers K) * d, mul_ne_zero (nonZeroDivisors.ne_zero m.2) hd, ?_⟩
    have key : ((m : NumberField.RingOfIntegers K) * d) • (a • x) = n • (d • x) := by
      rw [← algebraMap_smul K ((m : NumberField.RingOfIntegers K) * d) (a • x),
        ← algebraMap_smul K n (d • x), ← algebraMap_smul K d x, smul_smul, smul_smul, map_mul]
      congr 1
      rw [← hm]
      ring
    rw [key]
    exact L.smul_mem n h

end Bl.general_b_fact_left''''''''
