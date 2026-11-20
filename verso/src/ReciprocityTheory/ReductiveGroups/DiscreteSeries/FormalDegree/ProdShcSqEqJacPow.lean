import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPaHadApply
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ShcAdC
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPPos

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PolarJacobianDeterminant

/- English proof (translation)
Use `set f : Fin n → Fin n → ℝ := fun i j => shc (pev z i - pev z j) with hf`. Establish `hsym : ∀ i j, f i j = f j i`. Introduce `i j`. Simplify using `only [hf]`. Rewrite using `[← neg_sub, PolarJacobianDeterminant.shc_neg]`.

Establish `hpt : ∀ i j, f i j = (if i < j then f i j else 1) * (if j < i then f i j else 1)`. Introduce `i j`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Simplify using `[h, not_lt_of_gt h]`. Substitute `h` using the available equality.

Simplify using `[hf, shc]`. Simplify using `[h, not_lt_of_gt h]`. Establish `hswap : ∏ i, ∏ j, (if j < i then f i j else 1) = ∏ i, ∏ j, (if i < j then f i j else 1)`. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hsym]`. Establish `hJ : Jac z = ∏ i, ∏ j, (if i < j then f i j else 1)`. Simplify using `only [Jac, Finset.prod_filter, hf]`. Establish `hall : ∏ i, ∏ j, f i j = Jac z ^ 2`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.prod_mul_distrib]`. Use `_ = Jac z ^ 2 := by rw [hswap, ← hJ, sq]`. Establish `: ∏ i, ∏ j, shc (pev z i - pev z j) ^ 2 = (∏ i, ∏ j, f i j) ^ 2`. Simplify using `only [hf, Finset.prod_pow]`. Rewrite using `[this, hall, ← pow_mul]`.
-/
theorem prod_shc_sq_eq_Jac_pow {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    ∏ i, ∏ j, shc (pev z i - pev z j) ^ 2 = Jac z ^ 4 := by
  set f : Fin n → Fin n → ℝ := fun i j => shc (pev z i - pev z j) with hf
  have hsym : ∀ i j, f i j = f j i := by
    intro i j; simp only [hf]; rw [← neg_sub, PolarJacobianDeterminant.shc_neg]
  have hpt : ∀ i j, f i j = (if i < j then f i j else 1) * (if j < i then f i j else 1) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst h; simp [hf, shc]
    · simp [h, not_lt_of_gt h]
  have hswap : ∏ i, ∏ j, (if j < i then f i j else 1) = ∏ i, ∏ j, (if i < j then f i j else 1) := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    rw [hsym]
  have hJ : Jac z = ∏ i, ∏ j, (if i < j then f i j else 1) := by
    simp only [Jac, Finset.prod_filter, hf]
  have hall : ∏ i, ∏ j, f i j = Jac z ^ 2 := by
    calc ∏ i, ∏ j, f i j
          = ∏ i, ∏ j, ((if i < j then f i j else 1) * (if j < i then f i j else 1)) :=
          Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hpt i j
      _ = (∏ i, ∏ j, (if i < j then f i j else 1)) * ∏ i, ∏ j, (if j < i then f i j else 1) := by
          simp only [Finset.prod_mul_distrib]
      _ = Jac z ^ 2 := by rw [hswap, ← hJ, sq]
  have : ∏ i, ∏ j, shc (pev z i - pev z j) ^ 2 = (∏ i, ∏ j, f i j) ^ 2 := by
    simp only [hf, Finset.prod_pow]
  rw [this, hall, ← pow_mul]

/- English proof (translation)
Establish `: shcAdC y = ⇑(LinearMap.toContinuousLinearMap (PolarJacobianDeterminant.shcAdCL y))`. Use function extensionality and compare the values at `w`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `ContinuousLinearMap.fderiv _`.
-/
theorem fderiv_shcAdC {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    fderiv ℝ (shcAdC y) 0 = LinearMap.toContinuousLinearMap (PolarJacobianDeterminant.shcAdCL y) := by
  have : shcAdC y = ⇑(LinearMap.toContinuousLinearMap (PolarJacobianDeterminant.shcAdCL y)) := by
    funext w; rfl
  rw [this]
  exact ContinuousLinearMap.fderiv _

end PolarJacobianDeterminant

/- English proof (translation)
Establish `h4` using `(detPb y).symm.trans ((detPa y).trans (PolarJacobianDeterminant.prod_shc_sq_eq_Jac_pow y))`. Establish `hpos : 0 < LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))`. Rewrite using `[PolarJacobianDeterminant.fderiv_shcAdC, LinearMap.coe_toContinuousLinearMap]`. Conclude with `PolarJacobianDeterminant.det_shcAdCL_pos y`. Establish `hJ : 0 ≤ Jac y` using `Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ => (PolarJacobianDeterminant.shc_pos _).le`.

Conclude with `(pow_left_inj₀ hpos.le hJ (by norm_num)).mp h4`.
-/
theorem detP {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
      (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) = Jac y := by
  have h4 := (detPb y).symm.trans ((detPa y).trans (PolarJacobianDeterminant.prod_shc_sq_eq_Jac_pow y))
  have hpos : 0 < LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
      (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) := by
    rw [PolarJacobianDeterminant.fderiv_shcAdC, LinearMap.coe_toContinuousLinearMap]
    exact PolarJacobianDeterminant.det_shcAdCL_pos y
  have hJ : 0 ≤ Jac y := Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ =>
    (PolarJacobianDeterminant.shc_pos _).le
  exact (pow_left_inj₀ hpos.le hJ (by norm_num)).mp h4

end ReciprocityTheory.ChartRestriction.DS
