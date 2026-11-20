import Mathlib

namespace Bl.general_b_fact_right_alt_form

/- English proof (translation)
Introduce `E _ _ V _ _ _ _ A y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩`. Consider the case `add x z _ _ hx hz`.

Take `⟨d1, hd1, h1⟩` from `hx`. Take `⟨d2, hd2, h2⟩` from `hz`. Use `⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩` and prove the remaining obligations. Establish `e1 : (d1 * d2) • x = d2 • (d1 • x)` using `by rw [mul_comm, mul_smul]`. Establish `e2 : (d1 * d2) • z = d1 • (d2 • z)` using `by rw [mul_smul]`.

Rewrite using `[smul_add, e1, e2]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)`. Consider the case `smul c x _ hx`. Take `⟨d, hd, h⟩` from `hx`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c`.

Establish `hb : (b : NumberField.RingOfIntegers E) ≠ 0` using `nonZeroDivisors.coe_ne_zero b`. Use `⟨(b : NumberField.RingOfIntegers E) * d, mul_ne_zero hb hd, ?_⟩` and prove the remaining obligations. Establish `key : ((b : NumberField.RingOfIntegers E) * d) • (c • x) = a • (d • x)`. Rewrite using `[← algebraMap_smul E ((b : NumberField.RingOfIntegers E) * d), ← algebraMap_smul E a, ← algebraMap_smul E d, smul_smul, smul_smul, map_mul]`. Use `congr 1`.

Simplify using `only at hab`. Rewrite using `[← hab]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `Submodule.smul_mem _ _ h`.
-/
theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} E V] [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} E) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E V] (A : Set.{0} V) (y : V),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} E A) y →
    Exists.{1} fun (d : NumberField.RingOfIntegers.{0} E) ↦
      And (Ne.{1} d 0)
        (Membership.mem.{0, 0} (Submodule.span.{0, 0} (NumberField.RingOfIntegers.{0} E) A) (HSMul.hSMul.{0, 0, 0} d y)) := by
  intro E _ _ V _ _ _ _ A y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add x z _ _ hx hz =>
    obtain ⟨d1, hd1, h1⟩ := hx
    obtain ⟨d2, hd2, h2⟩ := hz
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    have e1 : (d1 * d2) • x = d2 • (d1 • x) := by rw [mul_comm, mul_smul]
    have e2 : (d1 * d2) • z = d1 • (d2 • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c
    have hb : (b : NumberField.RingOfIntegers E) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    refine ⟨(b : NumberField.RingOfIntegers E) * d, mul_ne_zero hb hd, ?_⟩
    have key : ((b : NumberField.RingOfIntegers E) * d) • (c • x) = a • (d • x) := by
      rw [← algebraMap_smul E ((b : NumberField.RingOfIntegers E) * d), ← algebraMap_smul E a,
        ← algebraMap_smul E d, smul_smul, smul_smul, map_mul]
      congr 1
      simp only at hab
      rw [← hab]
      ring
    rw [key]
    exact Submodule.smul_mem _ _ h

end Bl.general_b_fact_right_alt_form
