import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameDetNeZero
open GlobalTheory.WholeFlag GlobalTheory.WholeFlag.Glue
open scoped Matrix

set_option autoImplicit false

namespace GlobalTheory.WholeFlag.Glue

/- English proof (translation)
Use `symm`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul _ hJ]`. Conclude with `Matrix.map_one _ (map_zero f) (map_one f)`.
-/
theorem map_inv_of_isUnit_det_local {R S n : Type} [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]
    (f : R →+* S) (J : Matrix n n R) (hJ : IsUnit J.det) : (J⁻¹).map f = (J.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hJ]
  exact Matrix.map_one _ (map_zero f) (map_one f)

/- English proof (translation)
Establish `hA : (antiDiag R g).map f = antiDiag S g`. Use extensionality with `i k`. Simplify using `only [antiDiag, Matrix.map_apply, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Use extensionality with `r c`.

Use `Fin.addCases (fun k => ?_) (fun k => ?_) c` and prove the remaining obligations. Rewrite using `[Matrix.map_apply, fullFrame_left, fullFrame_left, Matrix.map_apply]`. Rewrite using `[Matrix.map_apply, fullFrame_right, fullFrame_right, ← map_inv_of_isUnit_det_local f J hJ, ← hA, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]`.
-/
theorem fullFrame_map_of_isUnit_det_local {R S : Type} [CommRing R] [CommRing S] {g : ℕ} (f : R →+* S)
    (U : Matrix (Fin (g + g)) (Fin g) R) (J : Matrix (Fin (g + g)) (Fin (g + g)) R)
    (Lft : Matrix (Fin g) (Fin (g + g)) R) (hJ : IsUnit J.det) :
    (fullFrame U J Lft).map f = fullFrame (U.map f) (J.map f) (Lft.map f) := by
  have hA : (antiDiag R g).map f = antiDiag S g := by
    ext i k
    simp only [antiDiag, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  ext r c
  refine Fin.addCases (fun k => ?_) (fun k => ?_) c
  · rw [Matrix.map_apply, fullFrame_left, fullFrame_left, Matrix.map_apply]
  · rw [Matrix.map_apply, fullFrame_right, fullFrame_right, ← map_inv_of_isUnit_det_local f J hJ, ← hA,
      ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]

/- English proof (translation)
Introduce `R _ _ g U J τ hJ hU hiso`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, fullFrame_map_of_isUnit_det_local _ _ _ _ hJ]`. Apply `fullFrame_det_ne_zero_field` to reduce the goal to its premises. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `hJ.map _`.

Rewrite using `[← Matrix.map_mul]`. Establish `h : leftInv U τ * U = 1`. Establish `h0 : leftInv U τ = (rowSel τ * U : Matrix (Fin g) (Fin g) R)⁻¹ * (rowSel τ : Matrix (Fin g) (Fin (g + g)) R)` using `rfl`. Rewrite using `[h0, Matrix.mul_assoc]`. Conclude with `Matrix.nonsing_inv_mul _ hU`.

Rewrite using `[h]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Rewrite using `[← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]`. Use extensionality with `i k`. Rewrite using `[Matrix.map_apply, Matrix.zero_apply, IsLocalRing.residue_eq_zero_iff]`.

Conclude with `hiso i k`.
-/
theorem isUnit_det_fullFrame_local : ∀ {R : Type} [CommRing R] [IsLocalRing R] {g : ℕ} (U : Matrix (Fin (g + g)) (Fin g) R) (J : Matrix (Fin (g + g)) (Fin (g + g)) R) (τ : Fin g → Fin (g + g)), IsUnit J.det → IsUnit (rowSel τ * U : Matrix (Fin g) (Fin g) R).det → (∀ i k, (U.transpose * J * U) i k ∈ IsLocalRing.maximalIdeal R) → IsUnit (fullFrame U J (leftInv U τ)).det := by
  intro R _ _ g U J τ hJ hU hiso
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply,
    fullFrame_map_of_isUnit_det_local _ _ _ _ hJ]
  apply fullFrame_det_ne_zero_field
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hJ.map _
  · rw [← Matrix.map_mul]
    have h : leftInv U τ * U = 1 := by
      have h0 : leftInv U τ = (rowSel τ * U : Matrix (Fin g) (Fin g) R)⁻¹ *
          (rowSel τ : Matrix (Fin g) (Fin (g + g)) R) := rfl
      rw [h0, Matrix.mul_assoc]
      exact Matrix.nonsing_inv_mul _ hU
    rw [h]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
    ext i k
    rw [Matrix.map_apply, Matrix.zero_apply, IsLocalRing.residue_eq_zero_iff]
    exact hiso i k

end GlobalTheory.WholeFlag.Glue
