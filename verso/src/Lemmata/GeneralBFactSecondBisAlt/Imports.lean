import Mathlib

namespace Bl.general_b_fact_second''''''''

/- English proof (translation)
Introduce `K _ _ V _ _ _ _ M x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨d1, hd1, h1⟩` from `hy`. Take `⟨d2, hd2, h2⟩` from `hz`. Use `⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Apply `M.add_mem` to reduce the goal to its premises.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `M.smul_mem _ h1`. Rewrite using `[mul_smul]`. Conclude with `M.smul_mem _ h2`. Consider the case `smul a y _ hy`.

Take `⟨d, hd, h⟩` from `hy`. Take `⟨⟨n, m⟩, hnm⟩` from `IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a`. Simplify using `only at hnm`. Use `⟨(m : NumberField.RingOfIntegers K) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero m) hd, ?_⟩` and prove the remaining obligations. Establish `e : ∀ (r : NumberField.RingOfIntegers K) (v : V), r • v = (algebraMap (NumberField.RingOfIntegers K) K r) • v` using `fun r v => (algebraMap_smul K r v).symm`.

Establish `key : ((m : NumberField.RingOfIntegers K) * d) • (a • y) = n • (d • y)`. Simplify using `only [e, smul_smul]`. Use `congr 1`. Rewrite using `[← hnm]`. Simplify using `only [map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `M.smul_mem _ h`.
-/
theorem goal1 :
  ∀ {K : Type} [inst : Field.{0} K] [NumberField.{0} K] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} K V] [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} K) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K V]
  (M : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) V) {x : V},
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} M)) x →
    Exists.{1} fun (d : NumberField.RingOfIntegers.{0} K) ↦
      And (Ne.{1} d 0) (Membership.mem.{0, 0} M (HSMul.hSMul.{0, 0, 0} d x)) := by
  intro K _ _ V _ _ _ _ M x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d1, hd1, h1⟩ := hy
    obtain ⟨d2, hd2, h2⟩ := hz
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    rw [smul_add]
    apply M.add_mem
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h1
    · rw [mul_smul]; exact M.smul_mem _ h2
  | smul a y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨n, m⟩, hnm⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a
    dsimp only at hnm
    refine ⟨(m : NumberField.RingOfIntegers K) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero m) hd, ?_⟩
    have e : ∀ (r : NumberField.RingOfIntegers K) (v : V),
        r • v = (algebraMap (NumberField.RingOfIntegers K) K r) • v :=
      fun r v => (algebraMap_smul K r v).symm
    have key : ((m : NumberField.RingOfIntegers K) * d) • (a • y) = n • (d • y) := by
      simp only [e, smul_smul]
      congr 1
      rw [← hnm]
      simp only [map_mul]
      ring
    rw [key]
    exact M.smul_mem _ h

end Bl.general_b_fact_second''''''''
