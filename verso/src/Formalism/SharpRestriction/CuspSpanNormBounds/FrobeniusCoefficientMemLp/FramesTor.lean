import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig

noncomputable section

namespace Formalism.MainNotions.S.Pv.Frames

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S

def dT (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then Complex.I ^ i.val else if r + k < i.val then Complex.I ^ (2 * r + k - i.val) else Complex.I ^ r

def tT (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.diagonal (dT k r)

def tTi (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.diagonal fun i => star (dT k r i)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem I_pow_unit (n : ℕ) : star (Complex.I ^ n) * Complex.I ^ n = 1 := by
  rw [star_pow, ← mul_pow]
  have h : star Complex.I * Complex.I = 1 := by
    rw [Complex.star_def, Complex.conj_I]; simp
  rw [h, one_pow]

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem dT_unit {k r : ℕ} (i : Fin (2 * r + k + 1)) : star (dT k r i) * dT k r i = 1 := by
  unfold dT
  split_ifs <;> exact I_pow_unit _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dT_unit' {k r : ℕ} (i : Fin (2 * r + k + 1)) : dT k r i * star (dT k r i) = 1 := by
  rw [mul_comm]; exact dT_unit i

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem tTi_mul_tT (k r : ℕ) : tTi k r * tT k r = 1 := by
  rw [tTi, tT, Matrix.diagonal_mul_diagonal]
  simp only [dT_unit]
  exact Matrix.diagonal_one

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem tT_mul_tTi (k r : ℕ) : tT k r * tTi k r = 1 := by
  rw [tTi, tT, Matrix.diagonal_mul_diagonal]
  simp only [dT_unit']
  exact Matrix.diagonal_one

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tT_inv (k r : ℕ) : (tT k r)⁻¹ = tTi k r := by
  exact Matrix.inv_eq_left_inv (tTi_mul_tT k r)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tTi_inv (k r : ℕ) : (tTi k r)⁻¹ = tT k r := by
  exact Matrix.inv_eq_left_inv (tT_mul_tTi k r)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem conjI_apply {k r : ℕ} (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (tTi k r * M * tT k r) i j = star (dT k r i) * M i j * dT k r j := by
  simp only [tTi, tT, Matrix.mul_diagonal, Matrix.diagonal_mul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem conj_apply {k r : ℕ} (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (tT k r * M * tTi k r) i j = dT k r i * M i j * star (dT k r j) := by
  simp only [tTi, tT, Matrix.mul_diagonal, Matrix.diagonal_mul]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem conjI_eq_self {k r : ℕ} {M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (h : ∀ i j, M i j ≠ 0 → dT k r i = dT k r j) : tTi k r * M * tT k r = M := by
  ext i j
  rw [conjI_apply]
  by_cases hM : M i j = 0
  · rw [hM, mul_zero, zero_mul]
  · rw [h i j hM, mul_comm (star (dT k r j)) (M i j), mul_assoc, dT_unit, mul_one]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem conj_eq_self {k r : ℕ} {M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (h : ∀ i j, M i j ≠ 0 → dT k r i = dT k r j) : tT k r * M * tTi k r = M := by
  ext i j
  rw [conj_apply]
  by_cases hM : M i j = 0
  · rw [hM, mul_zero, zero_mul]
  · rw [h i j hM, mul_comm (dT k r j) (M i j), mul_assoc, dT_unit', mul_one]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem dT_eI {k r : ℕ} (a : Fin r) : dT k r (eI k r a) = Complex.I ^ a.val := by
  have ha := a.isLt
  simp [dT, eI, ha]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem dT_esI {k r : ℕ} (a : Fin r) : dT k r (esI k r a) = Complex.I ^ a.val := by
  have ha := a.isLt
  have h1 : ¬ (2 * r + k - a.val < r) := by omega
  have h2 : r + k < 2 * r + k - a.val := by omega
  have h3 : 2 * r + k - (2 * r + k - a.val) = a.val := by omega
  simp [dT, esI, h1, h2, h3]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem dT_mid {k r : ℕ} (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : dT k r i = Complex.I ^ r := by
  unfold dT
  rw [if_neg (by omega), if_neg (by omega)]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers.
-/
theorem dT_pair {k r : ℕ} (i j : Fin (2 * r + k + 1)) (hi : i.val < r) (hij : i.val + j.val = 2 * r + k) :
    dT k r j = dT k r i := by
  have hj := j.isLt
  unfold dT
  rw [if_neg (by omega), if_pos (by omega), if_pos hi]
  congr 1
  omega

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Hpk_ne_dT {k r : ℕ} (i j : Fin (2 * r + k + 1)) (h : Hpk k r i j ≠ 0) : dT k r i = dT k r j := by
  unfold Hpk at h
  split_ifs at h with h1 h2 h3 h4
  · exact (dT_pair i j h1.1 h1.2).symm
  · exact dT_pair j i h2.1 (by have := h2.2; omega)
  · rw [h3.2.2]
  · rw [h3.2.2]
  · exact absurd rfl h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem conjT_tT (k r : ℕ) : (tT k r)ᴴ = tTi k r := by
  rw [tT, tTi, Matrix.diagonal_conjTranspose]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem conjT_tTi (k r : ℕ) : (tTi k r)ᴴ = tT k r := by
  rw [tT, tTi, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem tT_mem_UH (k r : ℕ) : tT k r ∈ UH (Hpk k r) := by
  show (tT k r)ᴴ * Hpk k r * tT k r = Hpk k r
  rw [conjT_tT]
  exact conjI_eq_self (fun i j h => Hpk_ne_dT i j h)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem tTi_mem_UH (k r : ℕ) : tTi k r ∈ UH (Hpk k r) := by
  show (tTi k r)ᴴ * Hpk k r * tTi k r = Hpk k r
  rw [conjT_tTi]
  exact conj_eq_self (fun i j h => Hpk_ne_dT i j h)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UH_mul {k r : ℕ} {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    (hh : h ∈ UH (Hpk k r)) : g * h ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  calc (g * h)ᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg']; exact hh'

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem tT_unitary (k r : ℕ) : tT k r ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjT_tT, tT_mul_tTi]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem tTi_unitary (k r : ℕ) : tTi k r ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjT_tTi, tTi_mul_tT]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem tT_mulVec_Wb {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    tT k r *ᵥ z = Complex.I ^ r • z := by
  funext i
  simp only [tT, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hz i hi, mul_zero, mul_zero]
  · push_neg at hi
    rw [dT_mid i hi.1 hi.2]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem tTi_mulVec_Wb {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    tTi k r *ᵥ z = star (Complex.I ^ r) • z := by
  funext i
  simp only [tTi, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hz i hi, mul_zero, mul_zero]
  · push_neg at hi
    rw [dT_mid i hi.1 hi.2]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem ell_conjI {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ell k r z (tTi k r * M * tT k r) = Complex.I * ell k r z M := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hu := I_pow_unit a.val
  split_ifs with h
  · rw [conjI_apply, dT_eI, dT_eI]
    show star (Complex.I ^ a.val) * M (eI k r a) (eI k r ⟨a.val + 1, h⟩) * Complex.I ^ (a.val + 1) =
      Complex.I * M (eI k r a) (eI k r ⟨a.val + 1, h⟩)
    rw [pow_succ]
    linear_combination (M (eI k r a) (eI k r ⟨a.val + 1, h⟩) * Complex.I) * hu
  · have ha := a.isLt
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tT_mulVec_Wb hz, Matrix.mulVec_smul]
    simp only [tTi, Matrix.mulVec_diagonal, dT_eI, Pi.smul_apply, smul_eq_mul]
    have hr : Complex.I ^ r = Complex.I ^ a.val * Complex.I := by
      rw [← pow_succ]; congr 1; omega
    rw [hr]
    linear_combination ((M *ᵥ z) (eI k r a) * Complex.I) * hu

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem psi_conjI {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {c c' : ℂ} (hc : c' * Complex.I = c)
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    psi k r z c' (tTi k r * M * tT k r) = psi k r z c M := by
  unfold psi
  rw [ell_conjI hz, ← mul_assoc, hc]

end Formalism.MainNotions.S.Pv.Frames

end
