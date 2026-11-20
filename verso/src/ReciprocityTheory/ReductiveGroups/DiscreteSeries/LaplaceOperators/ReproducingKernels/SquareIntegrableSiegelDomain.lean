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
Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega) | omega | norm_num`.
-/
theorem Hpk_out' (k r : ℕ) {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega) | omega | norm_num

/- English proof (translation)
Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega) | omega | norm_num`.
-/
theorem Hpk_mid' (k r : ℕ) {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega) | omega | norm_num

/- English proof (translation)
Rewrite using `[Matrix.mulVec, dotProduct]`. Distinguish the cases in `h : i.val < r ∨ r + k < i.val`. Rewrite using `[if_pos h]`. Simplify using `only [Hpk_out' k r h]`. Rewrite using `[Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]`.

Simplify using the standard rewrite rules. Introduce `j _ hj`. Rewrite using `[if_neg (fun h' => hj (Fin.ext h')), zero_mul]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg h]`.

Simplify using `only [Hpk_mid' k r h]`. Rewrite using `[Finset.sum_eq_single i]`. Apply the tactic sequence `split_ifs <;> simp_all`. Introduce `j _ hj`. Rewrite using `[if_neg (fun h' => hj (Fin.ext h')), zero_mul]`.

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
Use function extensionality and compare the values at `i`. Rewrite using `[Hpk_mulVec']`. Distinguish the cases in `h : i.val < r ∨ r + k < i.val`. Rewrite using `[if_pos h, Hpk_mulVec', if_pos (by simp only; omega)]`. Use `congr 1`.

Use `ext`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Apply the tactic sequence `rw [if_neg h, Hpk_mulVec', if_neg h] split_ifs <;> simp`.
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
Use extensionality with `i j`. Establish `h` using `congrFun (Hpk_mulVec_mulVec' k r (Pi.single j 1)) i`. Rewrite `h` using `[Matrix.mulVec_mulVec]`. Simplify `h` using `[Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply]`.
-/
theorem Hpk_sq' (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  have h := congrFun (Hpk_mulVec_mulVec' k r (Pi.single j 1)) i
  rw [Matrix.mulVec_mulVec] at h
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using h

/- English proof (translation)
Conclude with `IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, Hpk_sq', Matrix.det_one])`.
-/
theorem Hpk_det_unit (k r : ℕ) : IsUnit (Hpk k r).det := by
  exact IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, Hpk_sq', Matrix.det_one])

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (show aᴴ * Hpk k r * a = Hpk k r from ha)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul]`. Establish `hH` using `Hpk_det_unit k r`. Use `isUnit_iff_ne_zero.mpr fun h0 => ?_` and prove the remaining obligations. Rewrite `h` using `[h0, mul_zero]`.

Conclude with `hH.ne_zero h.symm`.
-/
theorem uh_det {k r : ℕ} {a : Mat k r} (ha : a ∈ UH (Hpk k r)) : IsUnit a.det := by
  have h := congrArg Matrix.det (show aᴴ * Hpk k r * a = Hpk k r from ha)
  rw [Matrix.det_mul, Matrix.det_mul] at h
  have hH := Hpk_det_unit k r
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at h
  exact hH.ne_zero h.symm

/- English proof (translation)
Establish `hu` using `uh_det ha`. Use `show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r`. Establish `ha' : aᴴ * Hpk k r * a = Hpk k r` using `ha`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by`. Rewrite using `[Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`.
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
Establish `h1 : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bG k r = bG k r`. Unfold `ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bG bG ReciprocityTheory.ChartRestriction.DS.Mult1.nR nS q0S ReciprocityTheory.ChartRestriction.DS.Mult1.S0.q0`. Both sides reduce to the same expression. Establish `h2 : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS k r ≤ bS k r`. Unfold `ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS bS nS ReciprocityTheory.ChartRestriction.DS.Mult1.S0.dimN`.

Use `push_cast`. Establish `h5 : 0 ≤ (r : ℝ) * (4 * r ^ 2 + 2 * r * k + 6 * r + 3 * k + 2)` using `by positivity`. Use polynomial arithmetic with `[h5]`. Establish `h3 : max (ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bG k r) (ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS k r) ≤ max (bG k r) (bS k r)` using `max_le_max h1.le h2`. Combine the linear equalities and inequalities to obtain the conclusion.
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
