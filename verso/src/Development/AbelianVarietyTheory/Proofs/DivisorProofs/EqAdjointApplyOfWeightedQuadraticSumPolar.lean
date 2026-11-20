import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

open GlobalTheory.Poinc Matrix

namespace GlobalTheory.Poinc

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem qW_polar_eq_sum_add_transpose {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (hβ : ∀ a b, β a b = β b a) (y z : Fin s → X) :
    qW W β (y + z) - qW W β y - qW W β z = ∑ u, ∑ v, (W + W.transpose) u v * β (y u) (z v) := by
  have h : ∑ u, ∑ v, W u v * β (z u) (y v) = ∑ u, ∑ v, W v u * β (y u) (z v) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hβ]
  simp only [qW, Pi.add_apply, map_add, LinearMap.add_apply, mul_add, add_mul, Finset.sum_add_distrib,
    Matrix.add_apply, Matrix.transpose_apply, h]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem eq_adjoint_apply_of_qW_polar (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : PosW W) (X₀ : Type) [AddCommGroup X₀]
    (β : LinearMap.BilinForm ℤ X₀) (hβ : ∀ a b, β a b = β b a) (hpos : ∀ a, a ≠ 0 → 0 < β a a)
    (E E' : Matrix (Fin 8) (Fin 8) ℤ) (hE : (W + W.transpose) * E' = E.transpose * (W + W.transpose))
    (z z' : Fin 8 → X₀)
    (h : ∀ y : Fin 8 → X₀, qW W β ((fun a => ∑ b, E a b • y b) + z) - qW W β (fun a => ∑ b, E a b • y b) - qW W β z =
      qW W β (y + z') - qW W β y - qW W β z') :
    z' = fun a => ∑ b, E' a b • z b := by
  simp only [qW_polar_eq_sum_add_transpose W β hβ] at h
  unfold PosW at hW
  set M := W + W.transpose with hM
  have hdet : M.det ≠ 0 := by
    have h1 := hW.det_pos
    have h2 : (M.map (Int.cast : ℤ → ℝ)).det = (M.det : ℝ) := by
      rw [Int.cast_det]
    rw [h2] at h1
    intro h0
    simp [h0] at h1
  have key : ∀ x : X₀, (fun v => β x (z' v)) = E' *ᵥ (fun v => β x (z v)) := by
    intro x
    rw [← sub_eq_zero]
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hE, sub_eq_zero]
    funext w
    have h1 := h (Pi.single w x)
    have h2 : ∀ a, ∑ b, E a b • (Pi.single w x : Fin 8 → X₀) b = E a w • x := by
      intro a
      rw [Finset.sum_eq_single w] <;> simp +contextual [Pi.single_apply]
    have h3 : ∑ u, ∑ v, M u v * β ((Pi.single w x : Fin 8 → X₀) u) (z' v) = ∑ v, M w v * β x (z' v) := by
      rw [Finset.sum_eq_single w] <;> simp +contextual [Pi.single_apply]
    simp only [h2, h3, map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h1
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [← h1, Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  funext a
  rw [← sub_eq_zero]
  by_contra hne
  have h1 := hpos _ hne
  generalize hd : z' a - ∑ b, E' a b • z b = d at h1
  have h2 := congrFun (key d) a
  have h3 : β d d = 0 := by
    conv_lhs => rw [show β d d = β d (z' a - ∑ b, E' a b • z b) by rw [hd]]
    simp only [map_sub, map_sum, map_zsmul, smul_eq_mul, h2, Matrix.mulVec, dotProduct, sub_self]
  omega

end GlobalTheory.Poinc
