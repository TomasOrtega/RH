import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOfSkewHermitianTwist

open Matrix

namespace GlobalTheory.SimNormal

/- English proof (translation)
Use extensionality with `i j`. Establish `e` using `congrFun (congrFun h i) j`. Simplify using `only [diagonal_mul, mul_diagonal] at e ⊢`. Distinguish the cases in `hg : g i j = 0`. Simplify using `[hg]`.

Establish `: d i = d j` using `mul_right_cancel₀ hg (e.trans (mul_comm _ _))`. Rewrite using `[hf i j this, mul_comm]`.
-/
theorem diagonal_comm_of_comm {n : ℕ} {d f : Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (h : diagonal d * g = g * diagonal d) (hf : ∀ i j, d i = d j → f i = f j) :
    diagonal f * g = g * diagonal f := by
  ext i j
  have e := congrFun (congrFun h i) j
  simp only [diagonal_mul, mul_diagonal] at e ⊢
  by_cases hg : g i j = 0
  · simp [hg]
  · have : d i = d j := mul_right_cancel₀ hg (e.trans (mul_comm _ _))
    rw [hf i j this, mul_comm]

/- English proof (translation)
Introduce `n J P hJ hJd hP hpos`. Take `⟨Q₀, hQ₀⟩` from `GlobalTheory.ThK.SqIntMaxCpt.exists_congr_one hP hpos`. Use `set M := Q₀.1ᴴ * J * Q₀.1 with hMdef`. Establish `hM : M.IsHermitian` using `isHermitian_conjTranspose_mul_mul _ hJ`. Use `set U : Matrix (Fin n) (Fin n) ℂ := hM.eigenvectorUnitary.1 with hU`.

Establish `h1 : Uᴴ * U = 1` using `Matrix.mem_unitaryGroup_iff'.1 hM.eigenvectorUnitary.2`. Establish `h1' : U * Uᴴ = 1` using `Matrix.mem_unitaryGroup_iff.1 hM.eigenvectorUnitary.2`. Use `set d : Fin n → ℝ := hM.eigenvalues with hd`. Use `set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun i => (d i : ℂ) with hD`. Establish `h3 : Uᴴ * M * U = D`.

Use `hM.conjStarAlgAut_star_eigenvectorUnitary` as an intermediate fact. Simplify `this` using `[Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]`. Establish `hdne : ∀ i, d i ≠ 0`. Establish `hUd : Uᴴ.det * U.det = 1` using `by rw [← det_mul, h1, det_one]`. Establish `hQd : Q₀.1.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).1 Q₀.isUnit).ne_zero`.

Establish `hDd : D.det ≠ 0`. Rewrite using `[← h3, hMdef, det_mul, det_mul, det_mul, det_mul]`. Establish `hU1 : Uᴴ.det ≠ 0` using `left_ne_zero_of_mul_eq_one hUd`. Establish `hU2 : U.det ≠ 0` using `right_ne_zero_of_mul_eq_one hUd`. Establish `hQ2 : Q₀.1ᴴ.det ≠ 0` using `by rw [det_conjTranspose]; simpa using hQd`.

Simplify using `only [ne_eq, mul_eq_zero, not_or]`. The claim follows by propositional logic. Introduce `i hi`. Apply `hDd` to reduce the goal to its premises. Rewrite using `[hD, det_diagonal]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])`. Establish `hMU : U * D * Uᴴ = M`. Rewrite using `[← h3]`. Simplify using `only [← Matrix.mul_assoc, h1', Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, h1', Matrix.mul_one]`.

Use `set s : Fin n → ℝ := fun i => (Real.sqrt |d i|)⁻¹ with hs`. Establish `hsq : ∀ i, 0 < Real.sqrt |d i|` using `fun i => Real.sqrt_pos.2 (abs_pos.2 (hdne i))`. Set `S : GL (Fin n) ℂ` to `⟨diagonal fun i => (s i : ℂ), diagonal fun i => (Real.sqrt |d i| : ℂ), by`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Simplify using `only [hs, Complex.ofReal_inv]; exact inv_mul_cancel₀ (by exact_mod_cast (hsq i).ne'), by`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `only [hs, Complex.ofReal_inv]; exact mul_inv_cancel₀ (by exact_mod_cast (hsq i).ne')⟩`. Set `Ug : GL (Fin n) ℂ` to `⟨U, Uᴴ, h1', h1⟩`. Use `⟨fun i => decide (0 < d i), Q₀ * Ug * S, ?_, fun g hgP hgJ => ?_⟩` and prove the remaining obligations. Establish `hSh : (S.1)ᴴ = S.1` using `by show (diagonal fun i => (s i : ℂ))ᴴ = _`. Rewrite using `[diagonal_conjTranspose]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `: (Q₀ * Ug * S).1ᴴ * J * (Q₀ * Ug * S).1 = S.1 * (Uᴴ * M * U) * S.1`. Simplify using `only [Units.val_mul, conjTranspose_mul, hSh, Matrix.mul_assoc, hMdef]`.

Both sides reduce to the same expression. Rewrite using `[this, h3]`. Use `show diagonal _ * diagonal _ * diagonal _ = _`. Rewrite using `[diagonal_mul_diagonal, diagonal_mul_diagonal]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Establish `hsi : s i * s i = |d i|⁻¹`. Simplify using `only [hs]`. Rewrite using `[← mul_inv, Real.mul_self_sqrt (abs_nonneg _)]`. Establish `: (s i : ℂ) * d i * s i = ((d i * (s i * s i) : ℝ) : ℂ)` using `by push_cast; ring`.

Rewrite using `[this, hsi]`. Break down `lt_or_gt_of_ne (hdne i) with h | h` into its components or cases. Simplify using `[h, not_lt.2 h.le, abs_of_neg h, (hdne i)]`. Simplify using `[h, abs_of_pos h, (hdne i)]`. Establish `hi : (Q₀⁻¹).1ᴴ * Q₀.1ᴴ = 1`.

Rewrite using `[← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]`. Establish `hPi : (Q₀⁻¹).1ᴴ * (Q₀⁻¹).1 = P`. Use `congrArg (fun A => (Q₀⁻¹).1ᴴ * A * (Q₀⁻¹).1) hQ₀` as an intermediate fact. Simplify `this.symm` using `only [← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_one, Units.mul_inv_cancel_right]`. Establish `hJi : (Q₀⁻¹).1ᴴ * M * (Q₀⁻¹).1 = J`.

Rewrite using `[hMdef]`. Simplify using `only [← Matrix.mul_assoc, hi, Matrix.one_mul, Units.mul_inv_cancel_right]`. Use `set g' := Uᴴ * (Q₀⁻¹).1 * g * Q₀.1 * U with hg'`. Establish `hg'1 : g'ᴴ * g' = 1`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [hg', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]`. Use `_ = Uᴴ * (Q₀.1ᴴ * P * Q₀.1) * U := by`. Rewrite using `[h1', Matrix.mul_one, hPi, hgP]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hQ₀, Matrix.mul_one, h1]`.

Establish `hg'D : g'ᴴ * D * g' = D`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hg', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]`. Use `_ = Uᴴ * (Q₀.1ᴴ * J * Q₀.1) * U := by`. Rewrite using `[hMU, hJi, hgJ]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = D := by rw [← hMdef, h3]`. Establish `hg'2 : g' * g'ᴴ = 1` using `mul_eq_one_comm.1 hg'1`. Establish `hcomm : D * g' = g' * D`. Combine the equalities or inequalities in the displayed calculation.

Establish `hQinv : ((Q₀ * Ug * S)⁻¹).1 * g * (Q₀ * Ug * S).1 = (S⁻¹).1 * g' * S.1`. Simplify using `only [_root_.mul_inv_rev, Units.val_mul, hg', Matrix.mul_assoc]`. Both sides reduce to the same expression. Establish `hSc : (S⁻¹).1 * g' = g' * (S⁻¹).1` using `diagonal_comm_of_comm (f := fun i => (Real.sqrt |d i| : ℂ)) hcomm fun i j h => by`. Establish `: d i = d j` using `by exact_mod_cast h`.

Simplify using `[this]`. Establish `hfin : (S⁻¹).1 * g' * S.1 = g'`. Rewrite using `[hSc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]`. Rewrite using `[hQinv, hfin]`. Conclude with `hg'1`.
-/
theorem simultaneous_normal_form : ∀ {n : ℕ} {J P : Matrix (Fin n) (Fin n) ℂ}, J.IsHermitian → J.det ≠ 0 → P.IsHermitian →
    (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) →
    ∃ (ε : Fin n → Bool) (Q : GL (Fin n) ℂ), Q.1ᴴ * J * Q.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * P * g = P → gᴴ * J * g = J →
        ((Q⁻¹).1 * g * Q.1)ᴴ * ((Q⁻¹).1 * g * Q.1) = 1 := by
  intro n J P hJ hJd hP hpos
  obtain ⟨Q₀, hQ₀⟩ := GlobalTheory.ThK.SqIntMaxCpt.exists_congr_one hP hpos
  set M := Q₀.1ᴴ * J * Q₀.1 with hMdef
  have hM : M.IsHermitian := isHermitian_conjTranspose_mul_mul _ hJ
  set U : Matrix (Fin n) (Fin n) ℂ := hM.eigenvectorUnitary.1 with hU
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hM.eigenvectorUnitary.2
  have h1' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hM.eigenvectorUnitary.2
  set d : Fin n → ℝ := hM.eigenvalues with hd
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun i => (d i : ℂ) with hD
  have h3 : Uᴴ * M * U = D := by
    have := hM.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  have hdne : ∀ i, d i ≠ 0 := by
    have hUd : Uᴴ.det * U.det = 1 := by rw [← det_mul, h1, det_one]
    have hQd : Q₀.1.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 Q₀.isUnit).ne_zero
    have hDd : D.det ≠ 0 := by
      rw [← h3, hMdef, det_mul, det_mul, det_mul, det_mul]
      have hU1 : Uᴴ.det ≠ 0 := left_ne_zero_of_mul_eq_one hUd
      have hU2 : U.det ≠ 0 := right_ne_zero_of_mul_eq_one hUd
      have hQ2 : Q₀.1ᴴ.det ≠ 0 := by rw [det_conjTranspose]; simpa using hQd
      simp only [ne_eq, mul_eq_zero, not_or]; tauto
    intro i hi
    apply hDd
    rw [hD, det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hMU : U * D * Uᴴ = M := by
    rw [← h3]; simp only [← Matrix.mul_assoc, h1', Matrix.one_mul]; rw [Matrix.mul_assoc, h1', Matrix.mul_one]
  set s : Fin n → ℝ := fun i => (Real.sqrt |d i|)⁻¹ with hs
  have hsq : ∀ i, 0 < Real.sqrt |d i| := fun i => Real.sqrt_pos.2 (abs_pos.2 (hdne i))
  let S : GL (Fin n) ℂ := ⟨diagonal fun i => (s i : ℂ), diagonal fun i => (Real.sqrt |d i| : ℂ), by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
      simp only [hs, Complex.ofReal_inv]; exact inv_mul_cancel₀ (by exact_mod_cast (hsq i).ne'), by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
      simp only [hs, Complex.ofReal_inv]; exact mul_inv_cancel₀ (by exact_mod_cast (hsq i).ne')⟩
  let Ug : GL (Fin n) ℂ := ⟨U, Uᴴ, h1', h1⟩
  refine ⟨fun i => decide (0 < d i), Q₀ * Ug * S, ?_, fun g hgP hgJ => ?_⟩
  · have hSh : (S.1)ᴴ = S.1 := by
      show (diagonal fun i => (s i : ℂ))ᴴ = _
      rw [diagonal_conjTranspose]; congr 1; funext i; simp
    have : (Q₀ * Ug * S).1ᴴ * J * (Q₀ * Ug * S).1 = S.1 * (Uᴴ * M * U) * S.1 := by
      simp only [Units.val_mul, conjTranspose_mul, hSh, Matrix.mul_assoc, hMdef]; rfl
    rw [this, h3]
    show diagonal _ * diagonal _ * diagonal _ = _
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext i
    have hsi : s i * s i = |d i|⁻¹ := by
      simp only [hs]; rw [← mul_inv, Real.mul_self_sqrt (abs_nonneg _)]
    have : (s i : ℂ) * d i * s i = ((d i * (s i * s i) : ℝ) : ℂ) := by push_cast; ring
    rw [this, hsi]
    rcases lt_or_gt_of_ne (hdne i) with h | h
    · simp [h, not_lt.2 h.le, abs_of_neg h, (hdne i)]
    · simp [h, abs_of_pos h, (hdne i)]
  · have hi : (Q₀⁻¹).1ᴴ * Q₀.1ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    have hPi : (Q₀⁻¹).1ᴴ * (Q₀⁻¹).1 = P := by
      have := congrArg (fun A => (Q₀⁻¹).1ᴴ * A * (Q₀⁻¹).1) hQ₀
      simpa only [← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_one, Units.mul_inv_cancel_right] using this.symm
    have hJi : (Q₀⁻¹).1ᴴ * M * (Q₀⁻¹).1 = J := by
      rw [hMdef]
      simp only [← Matrix.mul_assoc, hi, Matrix.one_mul, Units.mul_inv_cancel_right]
    set g' := Uᴴ * (Q₀⁻¹).1 * g * Q₀.1 * U with hg'
    have hg'1 : g'ᴴ * g' = 1 := by
      calc g'ᴴ * g' = Uᴴ * Q₀.1ᴴ * (gᴴ * ((Q₀⁻¹).1ᴴ * (U * Uᴴ) * (Q₀⁻¹).1) * g) * Q₀.1 * U := by
            simp only [hg', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
        _ = Uᴴ * (Q₀.1ᴴ * P * Q₀.1) * U := by
            rw [h1', Matrix.mul_one, hPi, hgP]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hQ₀, Matrix.mul_one, h1]
    have hg'D : g'ᴴ * D * g' = D := by
      calc g'ᴴ * D * g' = Uᴴ * Q₀.1ᴴ * (gᴴ * ((Q₀⁻¹).1ᴴ * (U * D * Uᴴ) * (Q₀⁻¹).1) * g) * Q₀.1 * U := by
            simp only [hg', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
        _ = Uᴴ * (Q₀.1ᴴ * J * Q₀.1) * U := by
            rw [hMU, hJi, hgJ]; simp only [Matrix.mul_assoc]
        _ = D := by rw [← hMdef, h3]
    have hg'2 : g' * g'ᴴ = 1 := mul_eq_one_comm.1 hg'1
    have hcomm : D * g' = g' * D := by
      calc D * g' = g' * g'ᴴ * D * g' := by rw [hg'2, Matrix.one_mul]
        _ = g' * (g'ᴴ * D * g') := by simp only [Matrix.mul_assoc]
        _ = g' * D := by rw [hg'D]
    have hQinv : ((Q₀ * Ug * S)⁻¹).1 * g * (Q₀ * Ug * S).1 = (S⁻¹).1 * g' * S.1 := by
      simp only [_root_.mul_inv_rev, Units.val_mul, hg', Matrix.mul_assoc]; rfl
    have hSc : (S⁻¹).1 * g' = g' * (S⁻¹).1 :=
      diagonal_comm_of_comm (f := fun i => (Real.sqrt |d i| : ℂ)) hcomm fun i j h => by
        have : d i = d j := by exact_mod_cast h
        simp [this]
    have hfin : (S⁻¹).1 * g' * S.1 = g' := by
      rw [hSc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [hQinv, hfin]
    exact hg'1

end GlobalTheory.SimNormal
