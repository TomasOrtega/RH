import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommOfBezout
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.UnitDiscAlg

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def, zsmul_eq_mul, norm_mul, norm_prod]`. Establish `hs : ‖((Equiv.Perm.sign σ : ℤ) : E)‖ ≤ 1`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`.

Conclude with `mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hy _ _)`.
-/
theorem integ_det_le {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {m : ℕ}
    (y : Matrix (Fin m) (Fin m) E) (hy : ∀ i j, ‖y i j‖ ≤ 1) : ‖y.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul, norm_mul, norm_prod]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : E)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  exact mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hy _ _)

/- English proof (translation)
Introduce `E _ _ n x hx hdet`. Establish `hne : x.det ≠ 0`. Introduce `h`. Rewrite `hdet` using `[h, norm_zero]`. Conclude with `zero_ne_one hdet`.

Establish `hu : IsUnit x` using `(Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hne)`. Use `⟨hu, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, hdet, inv_one, one_mul, Matrix.adjugate_apply]`. Apply `integ_det_le` to reduce the goal to its premises. Introduce `a b`.

Rewrite using `[Matrix.updateRow_apply]`. Use `split_ifs`. Apply the tactic sequence `rw [Pi.single_apply] split_ifs <;> simp`. Conclude with `hx a b`.
-/
theorem isUnit_and_integ_inv_of_norm_det_eq_one :
    ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
      (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ = 1 →
      IsUnit x ∧ ∀ i j, ‖x⁻¹ i j‖ ≤ 1 := by
  intro E _ _ n x hx hdet
  have hne : x.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact zero_ne_one hdet
  have hu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hne)
  refine ⟨hu, fun i j => ?_⟩
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv,
    hdet, inv_one, one_mul, Matrix.adjugate_apply]
  apply integ_det_le
  intro a b
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs <;> simp
  · exact hx a b

end GlobalTheory.UnitDiscAlg
