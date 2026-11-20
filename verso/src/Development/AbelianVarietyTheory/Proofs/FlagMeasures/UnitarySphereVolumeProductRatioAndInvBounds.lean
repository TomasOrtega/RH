import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZetaProdSphereVolumeBounds
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.SphereRatio

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem sphV_succ (i : ℕ) : sphV (i + 1) = sphV i * (2 * Real.pi ^ (i + 1) / (i.factorial : ℝ)) := by
  unfold sphV
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Check the signs of the components of the expression.
-/
theorem sphV_pos (i : ℕ) : 0 < sphV i := by
  unfold sphV
  refine Finset.prod_pos fun l _ => ?_
  have := Real.pi_pos
  positivity

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Evaluate the numerical expressions.
-/
theorem le_exp : (32.5 : ℝ) ≤ Real.exp 3.49 := by
  have h := Real.sum_le_exp_of_nonneg (x := (3.49 : ℝ)) (by norm_num) 10
  refine le_trans ?_ h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Put the polynomial expressions in normal form.
-/
theorem sphV_add_le (m j : ℕ) : sphV (m + j) ≤ sphV m * Real.exp (3.49 * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := GlobalTheory.zetaProd_sphereVolume_bounds.2.2 (m + j + 1) (by omega)
    rw [Nat.add_sub_cancel] at h
    have h2 := h.trans le_exp
    have hp := Real.pi_pos
    have hm := sphV_pos m
    rw [← add_assoc, sphV_succ]
    calc sphV (m + j) * (2 * Real.pi ^ (m + j + 1) / ((m + j).factorial : ℝ))
        ≤ (sphV m * Real.exp (3.49 * j)) * Real.exp 3.49 :=
          mul_le_mul ih h2 (by positivity) (by positivity)
      _ = sphV m * Real.exp (3.49 * ((j + 1 : ℕ) : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add]
          push_cast
          ring_nf

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem inv_sphV_le (J : ℕ) : (sphV J)⁻¹ ≤ (J : ℝ) ^ (J * (J - 1) / 2) := by
  induction J with
  | zero => simp [sphV]
  | succ J ih =>
    have hp : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have h1 : (1 : ℝ) ≤ 2 * Real.pi ^ (J + 1) := by
      have := one_le_pow₀ (n := J + 1) hp
      linarith
    have hf : (J.factorial : ℝ) ≤ (J : ℝ) ^ J := by exact_mod_cast Nat.factorial_le_pow J
    have h2 : (2 * Real.pi ^ (J + 1) / (J.factorial : ℝ))⁻¹ ≤ (J : ℝ) ^ J := by
      rw [inv_div]
      exact (div_le_self (by positivity) h1).trans hf
    have he : (J + 1) * (J + 1 - 1) / 2 = J * (J - 1) / 2 + J := Nat.triangle_succ J
    have hJ := sphV_pos J
    rw [sphV_succ, mul_inv, he]
    calc (sphV J)⁻¹ * (2 * Real.pi ^ (J + 1) / (J.factorial : ℝ))⁻¹
        ≤ (J : ℝ) ^ (J * (J - 1) / 2) * (J : ℝ) ^ J :=
          mul_le_mul ih h2 (by positivity) (by positivity)
      _ = (J : ℝ) ^ (J * (J - 1) / 2 + J) := by rw [pow_add]
      _ ≤ ((J + 1 : ℕ) : ℝ) ^ (J * (J - 1) / 2 + J) :=
          pow_le_pow_left₀ (by positivity) (by push_cast; linarith) _

end GlobalTheory.SphereRatio

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.sphV_ratio_and_inv_bounds :
    (∀ q j : ℕ, j ≤ q → Real.log (sphV q / sphV (q - j)) ≤ 3.49 * j) ∧
      ∀ J : ℕ, 0 < sphV J ∧ (sphV J)⁻¹ ≤ (J : ℝ) ^ (J * (J - 1) / 2) := by
  refine ⟨fun q j h => ?_, fun J => ⟨GlobalTheory.SphereRatio.sphV_pos J, GlobalTheory.SphereRatio.inv_sphV_le J⟩⟩
  have h1 := GlobalTheory.SphereRatio.sphV_add_le (q - j) j
  rw [Nat.sub_add_cancel h] at h1
  have hq := GlobalTheory.SphereRatio.sphV_pos q
  have hm := GlobalTheory.SphereRatio.sphV_pos (q - j)
  rw [Real.log_le_iff_le_exp (by positivity), div_le_iff₀ hm, mul_comm]
  exact h1
