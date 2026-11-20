import Mathlib

namespace Bl.general_b_fact_second_alt

/- English proof (translation)
Introduce `K _ _ r L v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Establish `h1 : (a * b) • x = b • (a • x)` using `by rw [mul_comm, mul_smul]`. Establish `h2 : (a * b) • y = a • (b • y)` using `mul_smul a b y`.

Rewrite using `[smul_add, h1, h2]`. Conclude with `L.add_mem (L.smul_mem b hax) (L.smul_mem a hby)`. Consider the case `smul c x _ hx`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨⟨n, d⟩, hnd⟩` from `IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) c`.

Use `⟨(d : NumberField.RingOfIntegers K) * a, mul_ne_zero (nonZeroDivisors.coe_ne_zero d) ha, ?_⟩` and prove the remaining obligations. Establish `key : ((d : NumberField.RingOfIntegers K) * a) • (c • x) = n • (a • x)`. Rewrite using `[← algebraMap_smul K ((d : NumberField.RingOfIntegers K) * a), ← algebraMap_smul K a, ← algebraMap_smul K n, smul_smul, smul_smul]`. Simplify using `only at hnd`. Rewrite using `[← hnd, map_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `L.smul_mem n hax`.
-/
theorem goal1 :
  ∀ {K : Type} [inst : Field.{0} K] [NumberField.{0} K] {r : Nat}
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) (Fin r → K)) (v : Fin r → K),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} L)) v →
    Exists.{1} fun (a : NumberField.RingOfIntegers.{0} K) ↦
      And (Ne.{1} a 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} a v)) := by
  intro K _ _ r L v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • y = a • (b • y) := mul_smul a b y
    rw [smul_add, h1, h2]
    exact L.add_mem (L.smul_mem b hax) (L.smul_mem a hby)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) c
    refine ⟨(d : NumberField.RingOfIntegers K) * a, mul_ne_zero (nonZeroDivisors.coe_ne_zero d) ha, ?_⟩
    have key : ((d : NumberField.RingOfIntegers K) * a) • (c • x) = n • (a • x) := by
      rw [← algebraMap_smul K ((d : NumberField.RingOfIntegers K) * a), ← algebraMap_smul K a,
        ← algebraMap_smul K n, smul_smul, smul_smul]
      simp only at hnd
      rw [← hnd, map_mul]
      congr 1
      ring
    rw [key]
    exact L.smul_mem n hax

end Bl.general_b_fact_second_alt
