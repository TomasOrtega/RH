import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PtParAnti

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

/- English proof (translation)
Establish `hfull : Formalism.L2.SG.RealObj.Dl Z (r + 1) = Z.det`. Unfold `Formalism.L2.SG.RealObj.Dl`. Rewrite using `[dif_pos le_rfl]`. Use `congr 1`. Establish `hr : Formalism.L2.SG.RealObj.Dl Z r = (Z.submatrix (Fin.last r).succAbove (Fin.last r).succAbove).det`.

Unfold `Formalism.L2.SG.RealObj.Dl`. Rewrite using `[dif_pos (Nat.le_succ r)]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Fin.succAbove_last]`.

Both sides reduce to the same expression. Rewrite using `[Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_fin_succ_eq_det_submatrix, hfull, hr]`. Establish `: ((-1 : ℂ) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1`. Rewrite using `[← two_mul, pow_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[this, one_mul]`.
-/
theorem inv_last {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Z⁻¹ (Fin.last r) (Fin.last r) = Ring.inverse (Formalism.L2.SG.RealObj.Dl Z (r + 1)) * Formalism.L2.SG.RealObj.Dl Z r := by
  have hfull : Formalism.L2.SG.RealObj.Dl Z (r + 1) = Z.det := by
    unfold Formalism.L2.SG.RealObj.Dl; rw [dif_pos le_rfl]
    congr 1
  have hr : Formalism.L2.SG.RealObj.Dl Z r = (Z.submatrix (Fin.last r).succAbove (Fin.last r).succAbove).det := by
    unfold Formalism.L2.SG.RealObj.Dl; rw [dif_pos (Nat.le_succ r)]
    congr 1; ext i j; simp only [Matrix.submatrix_apply, Fin.succAbove_last]; rfl
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_fin_succ_eq_det_submatrix, hfull, hr]
  have : ((-1 : ℂ) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]; simp
  rw [this, one_mul]

/- English proof (translation)
Establish `hfull : Formalism.L2.SG.RealObj.Dl Z (r + 1) = Z.det`. Unfold `Formalism.L2.SG.RealObj.Dl`. Rewrite using `[dif_pos le_rfl]`. Use `congr 1`. Establish `hd : Formalism.L2.SG.RealObj.Dl Z (r + 1) ≠ 0` using `by rw [hfull]; exact hZ.ne_zero`.

Rewrite using `[inv_last, Ring.inverse_eq_inv']`. Use `set d := Formalism.L2.SG.RealObj.Dl Z (r + 1)`. Use `set e := Formalism.L2.SG.RealObj.Dl Z r`. Establish `hdd : d * starRingEnd ℂ d ≠ 0` using `mul_ne_zero hd ((map_ne_zero _).2 hd)`. Introduce `h0`.

Establish `h1 : d * starRingEnd ℂ d - (T : ℂ) * T' * (e * starRingEnd ℂ e) = 0`. Establish `e1 : d * starRingEnd ℂ d - (T : ℂ) * T' * (e * starRingEnd ℂ e) = (d * starRingEnd ℂ d) * (1 - (T : ℂ) * T' * (d⁻¹ * e * starRingEnd ℂ (d⁻¹ * e)))`. Establish `hcd : starRingEnd ℂ d ≠ 0` using `(map_ne_zero _).2 hd`. Rewrite using `[map_mul, map_inv₀]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e1, h0, mul_zero]`. Establish `h2 : ((Complex.normSq d - T * T' * Complex.normSq e : ℝ) : ℂ) = 0`. Rewrite using `[← h1]`. Use `push_cast`. Rewrite using `[Complex.mul_conj, Complex.mul_conj]`.

Establish `h3 : Complex.normSq d - T * T' * Complex.normSq e = 0` using `by exact_mod_cast h2`. Unfold `Gv at hG`. Rewrite `hG` using `[Complex.sq_norm, Complex.sq_norm]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gap_of_G {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hZ : IsUnit Z.det) (T T' : ℝ)
    (hG : 0 < Gv T T' Z) :
    1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))) ≠ 0 := by
  have hfull : Formalism.L2.SG.RealObj.Dl Z (r + 1) = Z.det := by
    unfold Formalism.L2.SG.RealObj.Dl; rw [dif_pos le_rfl]
    congr 1
  have hd : Formalism.L2.SG.RealObj.Dl Z (r + 1) ≠ 0 := by rw [hfull]; exact hZ.ne_zero
  rw [inv_last, Ring.inverse_eq_inv']
  set d := Formalism.L2.SG.RealObj.Dl Z (r + 1)
  set e := Formalism.L2.SG.RealObj.Dl Z r
  have hdd : d * starRingEnd ℂ d ≠ 0 := mul_ne_zero hd ((map_ne_zero _).2 hd)
  intro h0
  have h1 : d * starRingEnd ℂ d - (T : ℂ) * T' * (e * starRingEnd ℂ e) = 0 := by
    have e1 : d * starRingEnd ℂ d - (T : ℂ) * T' * (e * starRingEnd ℂ e) =
        (d * starRingEnd ℂ d) * (1 - (T : ℂ) * T' * (d⁻¹ * e * starRingEnd ℂ (d⁻¹ * e))) := by
      have hcd : starRingEnd ℂ d ≠ 0 := (map_ne_zero _).2 hd
      rw [map_mul, map_inv₀]; field_simp
    rw [e1, h0, mul_zero]
  have h2 : ((Complex.normSq d - T * T' * Complex.normSq e : ℝ) : ℂ) = 0 := by
    rw [← h1]; push_cast; rw [Complex.mul_conj, Complex.mul_conj]
  have h3 : Complex.normSq d - T * T' * Complex.normSq e = 0 := by exact_mod_cast h2
  unfold Gv at hG
  rw [Complex.sq_norm, Complex.sq_norm] at hG
  linarith

end Formalism.L2.S.L6.UnitaryStandardVectors
