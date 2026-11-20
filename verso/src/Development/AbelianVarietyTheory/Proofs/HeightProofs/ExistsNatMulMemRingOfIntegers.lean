import Mathlib

namespace GlobalTheory.NatMulMemRingOfIntegers

/- English proof (translation)
Establish `h0 : Algebra.IsAlgebraic ℤ ℚ` using `IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)`. Establish `halg : IsAlgebraic ℤ e` using `(IsAlgebraic.of_finite ℚ e).restrictScalars ℤ`. Take `⟨y, hy0, hint⟩` from `halg.exists_integral_multiple`. Rewrite `hint` using `[zsmul_eq_mul]`. Break down `Int.natAbs_eq y with hy | hy` into its components or cases.

Use `⟨y.natAbs, Int.natAbs_pos.mpr hy0, ⟨(y : E) * e, (mem_integralClosure_iff ℤ E).mpr hint⟩, ?_⟩ show (y : E) * e = _` and prove the remaining obligations. Rewrite using `[congrArg (Int.cast : ℤ → E) hy, Int.cast_natCast]`. Use `⟨y.natAbs, Int.natAbs_pos.mpr hy0, ⟨-((y : E) * e), (mem_integralClosure_iff ℤ E).mpr hint.neg⟩, ?_⟩ show -((y : E) * e) = _` and prove the remaining obligations. Rewrite using `[congrArg (Int.cast : ℤ → E) hy, Int.cast_neg, Int.cast_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_nat_mul_mem_ringOfIntegers {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ (k : ℕ), 0 < k ∧ ∃ (r : NumberField.RingOfIntegers E), (r : E) = (k : E) * e := by
  have h0 : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have halg : IsAlgebraic ℤ e := (IsAlgebraic.of_finite ℚ e).restrictScalars ℤ
  obtain ⟨y, hy0, hint⟩ := halg.exists_integral_multiple
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with hy | hy
  · refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ⟨(y : E) * e, (mem_integralClosure_iff ℤ E).mpr hint⟩, ?_⟩
    show (y : E) * e = _
    rw [congrArg (Int.cast : ℤ → E) hy, Int.cast_natCast]
  · refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ⟨-((y : E) * e), (mem_integralClosure_iff ℤ E).mpr hint.neg⟩, ?_⟩
    show -((y : E) * e) = _
    rw [congrArg (Int.cast : ℤ → E) hy, Int.cast_neg, Int.cast_natCast]
    ring

end GlobalTheory.NatMulMemRingOfIntegers
