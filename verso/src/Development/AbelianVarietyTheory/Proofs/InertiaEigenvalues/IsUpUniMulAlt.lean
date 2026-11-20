import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds

universe u_1

namespace GlobalTheory.UpperUnipotentProductInertiaEigenvalues

/- English proof (translation)
Introduce `i j`. Use `⟨fun hji => ?_, fun hij => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge k i with hk | hk` into its components or cases.

Rewrite using `[(hU i k).1 hk, zero_mul]`. Rewrite using `[(hB k j).1 (lt_of_lt_of_le hji hk), mul_zero]`. Substitute `hij` using the available equality. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite using `[(hU i i).2 rfl, (hB i i).2 rfl, one_mul]`.

Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[(hU i k).1 h, zero_mul]`. Rewrite using `[(hB k i).1 h, mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem isUpUni_mul {K : Type u_1} [inst : CommRing K] {N : ℕ} {U B : Matrix (Fin N) (Fin N) K}
    (hU : Formalism.MainNotions.S.IsUpUni U) (hB : Formalism.MainNotions.S.IsUpUni B) : Formalism.MainNotions.S.IsUpUni (U * B) := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [(hU i k).1 hk, zero_mul]
    · rw [(hB k j).1 (lt_of_lt_of_le hji hk), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hU i i).2 rfl, (hB i i).2 rfl, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hU i k).1 h, zero_mul]
      · rw [(hB k i).1 h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

end GlobalTheory.UpperUnipotentProductInertiaEigenvalues
