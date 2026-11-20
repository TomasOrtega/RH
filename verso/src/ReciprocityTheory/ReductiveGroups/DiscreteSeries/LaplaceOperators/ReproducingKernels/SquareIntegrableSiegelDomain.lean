import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.BesselIntegralSquareIntegrable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.MuSHaar

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.HpkMatrixVectorIdentities

open Formalism.QuantumDeterminants

section frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

end frob

section hpk

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem Hpk_out' (k r : ℕ) {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega) | omega | norm_num

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem Hpk_mid' (k r : ℕ) {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega) | omega | norm_num

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem Hpk_mulVec' (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  rw [Matrix.mulVec, dotProduct]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h]
    simp only [Hpk_out' k r h]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro j _ hj
      rw [if_neg (fun h' => hj (Fin.ext h')), zero_mul]
    · simp
  · rw [if_neg h]
    simp only [Hpk_mid' k r h]
    rw [Finset.sum_eq_single i]
    · split_ifs <;> simp_all
    · intro j _ hj
      rw [if_neg (fun h' => hj (Fin.ext h')), zero_mul]
    · simp

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem Hpk_mulVec_mulVec' (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  rw [Hpk_mulVec']
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, Hpk_mulVec', if_pos (by simp only; omega)]
    congr 1
    ext
    simp only
    omega
  · rw [if_neg h, Hpk_mulVec', if_neg h]
    split_ifs <;> simp

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem Hpk_sq' (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  have h := congrFun (Hpk_mulVec_mulVec' k r (Pi.single j 1)) i
  rw [Matrix.mulVec_mulVec] at h
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Hpk_det_unit (k r : ℕ) : IsUnit (Hpk k r).det := by
  exact IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, Hpk_sq', Matrix.det_one])

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem uh_det {k r : ℕ} {a : Mat k r} (ha : a ∈ UH (Hpk k r)) : IsUnit a.det := by
  have h := congrArg Matrix.det (show aᴴ * Hpk k r * a = Hpk k r from ha)
  rw [Matrix.det_mul, Matrix.det_mul] at h
  have hH := Hpk_det_unit k r
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at h
  exact hH.ne_zero h.symm

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem uh_inv {k r : ℕ} {a : Mat k r} (ha : a ∈ UH (Hpk k r)) : a⁻¹ ∈ UH (Hpk k r) := by
  have hu := uh_det ha
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
      rw [Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

end hpk

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Both sides reduce to the same expression. Establish an intermediate fact. Replace the relevant objects with their definitions.

Move the embeddings inside the algebraic operations. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thr (k r : ℕ) (a : ℝ) (ha : 4 * max (bG k r) (bS k r) < a - 1) :
    4 * max (ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bG k r) (ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS k r) < a := by
  have h1 : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bG k r = bG k r := by
    unfold ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bG bG ReciprocityTheory.ChartRestriction.DS.Mult1.nR nS q0S ReciprocityTheory.ChartRestriction.DS.Mult1.S0.q0
    rfl
  have h2 : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS k r ≤ bS k r := by
    unfold ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS bS nS ReciprocityTheory.ChartRestriction.DS.Mult1.S0.dimN
    push_cast
    have h5 : 0 ≤ (r : ℝ) * (4 * r ^ 2 + 2 * r * k + 6 * r + 3 * k + 2) := by positivity
    nlinarith [h5]
  have h3 : max (ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bG k r) (ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS k r) ≤ max (bG k r) (bS k r) :=
    max_le_max h1.le h2
  linarith

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.HpkMatrixVectorIdentities
