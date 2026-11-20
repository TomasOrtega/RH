import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.FormalDegreeBessel.FinalG

universe u_1

namespace GlobalTheory.LowerUnipotentMul

open Matrix

/- English proof (translation)
Introduce `i j`. Prove the components needed by the constructor for the conclusion. Introduce `hij`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Break down `lt_or_ge i k with hik | hki` into its components or cases. Rewrite using `[(hl i k).1 hik, zero_mul]`. Rewrite using `[(hl' k j).1 (lt_of_le_of_lt hki hij), mul_zero]`. Introduce `hij`. Substitute `hij` using the available equality.

Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite using `[(hl i i).2 rfl, (hl' i i).2 rfl, one_mul]`. Introduce `k _ hki`. Break down `lt_or_gt_of_ne hki with h | h` into its components or cases. Rewrite using `[(hl' k i).1 h, mul_zero]`.

Rewrite using `[(hl i k).1 h, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem isLoUni_mul {R : Type*} [CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R}
    (hl : Formalism.MainNotions.S.IsLoUni l) (hl' : Formalism.MainNotions.S.IsLoUni l') : Formalism.MainNotions.S.IsLoUni (l * l') := by
  intro i j
  constructor
  · intro hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge i k with hik | hki
    · rw [(hl i k).1 hik, zero_mul]
    · rw [(hl' k j).1 (lt_of_le_of_lt hki hij), mul_zero]
  · intro hij
    subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hl i i).2 rfl, (hl' i i).2 rfl, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [(hl' k i).1 h, mul_zero]
      · rw [(hl i k).1 h, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Introduce `hl hl'` and use `isLoUni_mul hl hl'`.
-/
theorem main : ∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R},
    Formalism.MainNotions.S.IsLoUni l → Formalism.MainNotions.S.IsLoUni l' → Formalism.MainNotions.S.IsLoUni (l * l') :=
  fun hl hl' => isLoUni_mul hl hl'

end GlobalTheory.LowerUnipotentMul
