import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

/- English proof (translation)
Establish `h1 : ∀ a b : ZMod n, e (b * a) * e⁻¹ b = e (b * (a - 1))`. Introduce `a b`. Rewrite using `[AddChar.inv_apply, ← AddChar.map_add_eq_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show gaussSum χ⁻¹ e⁻¹ = ∑ b, χ⁻¹ b * e⁻¹ b from rfl, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[gaussSum_mulShift_of_isPrimitive e hχ]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = ∑ b, ∑ a, χ a * e (b * (a - 1)) := by`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[gaussSum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[AddChar.mulShift_apply, mul_assoc, h1]`.

Use `_ = ∑ a, χ a * ∑ b, e (b * (a - 1)) := by`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[Finset.mul_sum]`. Use `_ = ∑ a, χ a * (if a - 1 = 0 then (Fintype.card (ZMod n) : K) else 0) := by`. Repeatedly rewrite using `[AddChar.sum_mulShift _ he, Nat.cast_ite, Nat.cast_zero]`.

Use `_ = n := by`. Simplify using `[sub_eq_zero, ZMod.card]`.
-/
theorem gaussSum_mul_gaussSum_inv_prim {K : Type} [Field K] {n : ℕ} [NeZero n]
    {χ : DirichletCharacter K n} {e : AddChar (ZMod n) K} (hχ : χ.IsPrimitive)
    (he : e.IsPrimitive) : gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = (n : K) := by
  classical
  have h1 : ∀ a b : ZMod n, e (b * a) * e⁻¹ b = e (b * (a - 1)) := by
    intro a b
    rw [AddChar.inv_apply, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc gaussSum χ e * gaussSum χ⁻¹ e⁻¹
      = ∑ b, gaussSum χ (e.mulShift b) * e⁻¹ b := by
        rw [show gaussSum χ⁻¹ e⁻¹ = ∑ b, χ⁻¹ b * e⁻¹ b from rfl, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [gaussSum_mulShift_of_isPrimitive e hχ]
        ring
    _ = ∑ b, ∑ a, χ a * e (b * (a - 1)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [gaussSum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [AddChar.mulShift_apply, mul_assoc, h1]
    _ = ∑ a, χ a * ∑ b, e (b * (a - 1)) := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
    _ = ∑ a, χ a * (if a - 1 = 0 then (Fintype.card (ZMod n) : K) else 0) := by
        simp_rw [AddChar.sum_mulShift _ he, Nat.cast_ite, Nat.cast_zero]
    _ = n := by
        simp [sub_eq_zero, ZMod.card]

end GlobalTheory.KummerEisensteinGalois
