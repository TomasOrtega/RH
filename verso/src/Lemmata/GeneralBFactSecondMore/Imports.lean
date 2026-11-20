import Mathlib

namespace Bl.general_b_fact_second'

/- English proof (translation)
Introduce `E U _ _ _ _ _ _ N hN x`. Establish `hx : x ∈ Submodule.span E (N : Set U)` using `by rw [hN]; exact Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩`.

Consider the case `add y z _ _ hy hz`. Take `⟨d1, hd1, h1⟩` from `hy`. Take `⟨d2, hd2, h2⟩` from `hz`. Use `⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`.

Apply `N.add_mem` to reduce the goal to its premises. Rewrite using `[mul_comm, mul_smul]`. Conclude with `N.smul_mem d2 h1`. Rewrite using `[mul_smul]`. Conclude with `N.smul_mem d1 h2`.

Consider the case `smul a y _ hy`. Take `⟨d, hd, h⟩` from `hy`. Take `⟨⟨n, m⟩, hm⟩` from `IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) a`. Establish `key : ((m : NumberField.RingOfIntegers E)) • (a • y) = n • y`. Rewrite using `[← smul_assoc, Algebra.smul_def, mul_comm]`.

Simplify using `only at hm`. Rewrite using `[hm, algebraMap_smul]`. Use `⟨d * m, mul_ne_zero hd (nonZeroDivisors.coe_ne_zero m), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, key, ← mul_smul, mul_comm, mul_smul]`. Conclude with `N.smul_mem n h`.
-/
theorem goal1 :
  ∀ {E U : Type} [inst : Field.{0} E] [NumberField.{0} E] [inst_2 : AddCommGroup.{0} U] [inst_3 : Module.{0, 0} E U]
  [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} E) U]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E U]
  (N : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) U),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} N)) Top.top.{0} →
    ∀ (x : U),
      Exists.{1} fun (d : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} d 0) (Membership.mem.{0, 0} N (HSMul.hSMul.{0, 0, 0} d x)) := by
  intro E U _ _ _ _ _ _ N hN x
  have hx : x ∈ Submodule.span E (N : Set U) := by rw [hN]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨d1, hd1, h1⟩ := hy
    obtain ⟨d2, hd2, h2⟩ := hz
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    rw [smul_add]
    apply N.add_mem
    · rw [mul_comm, mul_smul]; exact N.smul_mem d2 h1
    · rw [mul_smul]; exact N.smul_mem d1 h2
  | smul a y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨n, m⟩, hm⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) a
    have key : ((m : NumberField.RingOfIntegers E)) • (a • y) = n • y := by
      rw [← smul_assoc, Algebra.smul_def, mul_comm]
      simp only at hm
      rw [hm, algebraMap_smul]
    refine ⟨d * m, mul_ne_zero hd (nonZeroDivisors.coe_ne_zero m), ?_⟩
    rw [mul_smul, key, ← mul_smul, mul_comm, mul_smul]
    exact N.smul_mem n h

end Bl.general_b_fact_second'
