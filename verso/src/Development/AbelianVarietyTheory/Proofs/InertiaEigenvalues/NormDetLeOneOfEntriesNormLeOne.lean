import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommOfBezout
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ n x hx`. Rewrite using `[Matrix.det_apply]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_` and prove the remaining obligations. Establish `hp : ‖∏ i, x (σ i) i‖ ≤ 1`. Rewrite using `[norm_prod]`.

Conclude with `Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hx _ _)`. Break down `Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h` into its components or cases. Rewrite using `[h, one_smul]`. Conclude with `hp`. Rewrite using `[h, Units.neg_smul, one_smul, norm_neg]`.

Conclude with `hp`.
-/
theorem norm_det_le_one_of_entries_le_one :
    ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
      (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ ≤ 1 := by
  intro E _ _ n x hx
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hp : ‖∏ i, x (σ i) i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hx _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact hp
  · rw [h, Units.neg_smul, one_smul, norm_neg]; exact hp

end GlobalTheory
