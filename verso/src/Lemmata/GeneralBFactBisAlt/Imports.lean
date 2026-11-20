import Mathlib

namespace Bl.general_b_fact_bis_other

/- English proof (translation)
Introduce `K _ _ r n v x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨d, hd, hd'⟩` from `hy`. Take `⟨e, he, he'⟩` from `hz`. Use `⟨d * e, mul_ne_zero hd he, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `zsmul_mem hd' e`. Rewrite using `[mul_smul]`. Conclude with `zsmul_mem he' d`. Consider the case `smul c y _ hy`.

Take `⟨d, hd, hd'⟩` from `hy`. Take `⟨e, he, hint⟩` from `((IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c)).exists_integral_multiple`. Use `⟨e * d, mul_ne_zero he hd, ?_⟩` and prove the remaining obligations. Establish `key : ((⟨e • c, hint⟩ : NumberField.RingOfIntegers K)) • (d • y) = (e * d) • (c • y)`. Rewrite using `[← algebraMap_smul K]`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]`. Express the relevant statement in the definitionally equal form `((e : K) * c) * ((d : K) * y i) = ((e * d : ℤ) : K) * (c * y i)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← key]`. Conclude with `Submodule.smul_mem _ _ hd'`.
-/
theorem goal1 :
  ∀ {K : Type} [inst : Field.{0} K] [NumberField.{0} K] {r n : Nat} (v : Fin n → Fin r → K) {x : Fin r → K},
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (Set.range.{0, 1} v)) x →
    Exists.{1} fun (d : Int) ↦
      And (Ne.{1} d 0)
        (Membership.mem.{0, 0} (Submodule.span.{0, 0} (NumberField.RingOfIntegers.{0} K) (Set.range.{0, 1} v))
          (HSMul.hSMul.{0, 0, 0} d x)) := by
  intro K _ _ r n v x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨d, hd, hd'⟩ := hy
    obtain ⟨e, he, he'⟩ := hz
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]
      exact zsmul_mem hd' e
    · rw [mul_smul]
      exact zsmul_mem he' d
  | smul c y _ hy =>
    obtain ⟨d, hd, hd'⟩ := hy
    obtain ⟨e, he, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c)).exists_integral_multiple
    refine ⟨e * d, mul_ne_zero he hd, ?_⟩
    have key : ((⟨e • c, hint⟩ : NumberField.RingOfIntegers K)) • (d • y) = (e * d) • (c • y) := by
      rw [← algebraMap_smul K]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]
      change ((e : K) * c) * ((d : K) * y i) = ((e * d : ℤ) : K) * (c * y i)
      push_cast
      ring
    rw [← key]
    exact Submodule.smul_mem _ _ hd'

end Bl.general_b_fact_bis_other
