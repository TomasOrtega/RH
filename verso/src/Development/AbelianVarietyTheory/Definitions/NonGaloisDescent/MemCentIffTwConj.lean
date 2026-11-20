import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwConj

open Matrix

noncomputable section

namespace GlobalTheory.Tw.Model

variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

omit [StarRing R] in
/- English proof (translation)
Simplify using `only [Phi, Matrix.of_apply]`. Use `congr 1`. Apply `propext` to reduce the goal to its premises. Rewrite using `[Fin.ext_iff, Fin.val_rev]`. Use `i.2` as an intermediate fact.

Use `j.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem Phi_apply' (i j : Fin n) : Phi n R i j = if j = i.rev then (-1) ^ (i : ℕ) else 0 := by
  simp only [Phi, Matrix.of_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff, Fin.val_rev]
  have := i.2
  have := j.2
  omega

omit [StarRing R] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Phi_apply', ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_inj, Matrix.one_apply]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[← pow_add, ← two_mul, pow_mul]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem Phi_mul_transpose : Phi n R * (Phi n R)ᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Phi_apply', ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_inj, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [← pow_add, ← two_mul, pow_mul]; simp
  · simp

omit [StarRing R] in
/- English proof (translation)
The claim follows from `mul_eq_one_comm.mp Phi_mul_transpose`.
-/
theorem transpose_mul_Phi : (Phi n R)ᵀ * Phi n R = 1 := mul_eq_one_comm.mp Phi_mul_transpose

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Phi_apply']`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Phi_conjTranspose : (Phi n R)ᴴ = (Phi n R)ᵀ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Phi_apply']
  split_ifs <;> simp

omit [StarRing R] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, Matrix.smul_apply, Phi, Matrix.of_apply, smul_eq_mul]`. Distinguish the cases in `h : (i : ℕ) + (j : ℕ) + 1 = n`. Rewrite using `[if_pos h, if_pos (by omega)]`. Establish `: n - 1 = i + j` using `by omega`.

Rewrite using `[this, ← pow_add, show (i : ℕ) + j + i = 2 * i + j by ring, pow_add, pow_mul]; simp`. Rewrite using `[if_neg h, if_neg (by omega)]; simp`.
-/
theorem Phi_transpose : (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • Phi n R := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, Phi, Matrix.of_apply, smul_eq_mul]
  by_cases h : (i : ℕ) + (j : ℕ) + 1 = n
  · rw [if_pos h, if_pos (by omega)]
    have : n - 1 = i + j := by omega
    rw [this, ← pow_add, show (i : ℕ) + j + i = 2 * i + j by ring, pow_add, pow_mul]; simp
  · rw [if_neg h, if_neg (by omega)]; simp

/- English proof (translation)
Simplify using `[theta, Phi_mul_transpose]`.
-/
theorem theta_one : theta (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp [theta, Phi_mul_transpose]

/- English proof (translation)
Simplify using `only [theta, Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (Phi n R)ᵀ (Phi n R), transpose_mul_Phi, Matrix.one_mul]`.
-/
theorem theta_mul (g h : Matrix (Fin n) (Fin n) R) : theta (g * h) = theta g * theta h := by
  simp only [theta, Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Phi n R)ᵀ (Phi n R), transpose_mul_Phi, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[← theta_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hg), theta_one]`.
-/
theorem theta_mul_theta_inv {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    theta g * theta g⁻¹ = 1 := by
  rw [← theta_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hg), theta_one]

/- English proof (translation)
Rewrite using `[Matrix.inv_eq_right_inv (theta_mul_theta_inv hg), theta, Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hg)]`.
-/
theorem theta_inv_eq {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    (theta g)⁻¹ = Phi n R * gᴴ * (Phi n R)ᵀ := by
  rw [Matrix.inv_eq_right_inv (theta_mul_theta_inv hg), theta,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hg)]

/- English proof (translation)
Rewrite using `[theta, theta_inv_eq hg]`. Establish `h2 : ((Phi n R)ᵀ)ᴴ = Phi n R` using `by rw [← Phi_conjTranspose, conjTranspose_conjTranspose]`. Simplify using `only [Matrix.conjTranspose_mul, conjTranspose_conjTranspose, h2, Phi_conjTranspose]`. Establish `hs : ((-1 : R) ^ (n - 1)) * ((-1 : R) ^ (n - 1)) = 1`. Rewrite using `[← pow_add, ← two_mul, pow_mul]`.

Simplify using the standard rewrite rules. Establish `hP : Phi n R = ((-1 : R) ^ (n - 1)) • (Phi n R)ᵀ`. Rewrite using `[Phi_transpose, smul_smul, hs, one_smul]`. Establish `h3 : Phi n R * Phi n R = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R)` using `by conv_lhs => rw [hP] nth_rewrite 2 [Phi_transpose]`. Rewrite using `[smul_smul, hs, one_smul, Matrix.smul_mul, transpose_mul_Phi]`.

Establish `h4 : (Phi n R)ᵀ * (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R)`. Rewrite using `[← Matrix.transpose_mul, h3]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.
-/
theorem theta_theta {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : theta (theta g) = g := by
  rw [theta, theta_inv_eq hg]
  have h2 : ((Phi n R)ᵀ)ᴴ = Phi n R := by rw [← Phi_conjTranspose, conjTranspose_conjTranspose]
  simp only [Matrix.conjTranspose_mul, conjTranspose_conjTranspose, h2, Phi_conjTranspose]
  have hs : ((-1 : R) ^ (n - 1)) * ((-1 : R) ^ (n - 1)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have hP : Phi n R = ((-1 : R) ^ (n - 1)) • (Phi n R)ᵀ := by
    rw [Phi_transpose, smul_smul, hs, one_smul]
  have h3 : Phi n R * Phi n R = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
    conv_lhs => rw [hP]
    nth_rewrite 2 [Phi_transpose]
    rw [smul_smul, hs, one_smul, Matrix.smul_mul, transpose_mul_Phi]
  have h4 : (Phi n R)ᵀ * (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← Matrix.transpose_mul, h3]; simp
  calc Phi n R * (Phi n R * (g * (Phi n R)ᵀ)) * (Phi n R)ᵀ
      = (Phi n R * Phi n R) * g * ((Phi n R)ᵀ * (Phi n R)ᵀ) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h3, h4]; simp [smul_smul, hs]

/- English proof (translation)
Establish `hx' : IsUnit x⁻¹` using `by rwa [Matrix.isUnit_nonsing_inv_iff]`. Simplify using `only [nrm, twConj, theta_mul, theta_theta hx, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (theta x), theta_mul_theta_inv hx, Matrix.one_mul]`.
-/
theorem nrm_twConj {x δ : Matrix (Fin n) (Fin n) R} (hx : IsUnit x) :
    nrm (twConj x δ) = x⁻¹ * nrm δ * x := by
  have hx' : IsUnit x⁻¹ := by rwa [Matrix.isUnit_nonsing_inv_iff]
  simp only [nrm, twConj, theta_mul, theta_theta hx, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (theta x), theta_mul_theta_inv hx, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_inv_rev, theta_inv_eq hg, Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det δ).mp hδ), adj]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem adj_eq {δ g : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (hg : IsUnit g) :
    adj δ g = (δ * theta g * δ⁻¹)⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, theta_inv_eq hg,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det δ).mp hδ), adj]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish `hd` using `(Matrix.isUnit_iff_isUnit_det g).mp hg`. Simplify using `only [cent, Set.mem_setOf_eq, hg, true_and, twConj, Matrix.mul_assoc]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← h, Matrix.nonsing_inv_mul_cancel_left _ _ hd]`.

Introduce `h conv_lhs => rw [← h]`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ hd]`.
-/
theorem mem_cent_iff_twConj {δ g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    g ∈ cent δ ↔ twConj g δ = δ := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).mp hg
  simp only [cent, Set.mem_setOf_eq, hg, true_and, twConj, Matrix.mul_assoc]
  constructor
  · intro h
    rw [← h, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hd]

/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Phi]`.
-/
theorem Phi_two : Phi 2 ℂ = !![0, 1; -1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Phi]

/- English proof (translation)
Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem inv_diag : (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = !![1/2, 0; 0, 1] := by
  apply Matrix.inv_eq_right_inv
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Rewrite using `[nrm, theta, inv_diag, Phi_two]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct, map_ofNat]`.
-/
theorem nrm_diag : nrm (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal ![2, 1/2] := by
  rw [nrm, theta, inv_diag, Phi_two]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct, map_ofNat]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Simplify using `[Matrix.det_fin_two]`. Rewrite using `[nrm_diag, Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]`. Introduce `i j h`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all <;> norm_num at h`.
-/
theorem reg_diag : Reg (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det]; simp [Matrix.det_fin_two]
  · rw [nrm_diag, Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all <;> norm_num at h

/- English proof (translation)
Introduce and unpack `⟨-, h⟩`. Rewrite `h` using `[nrm, theta_one, Matrix.mul_one, ← Matrix.diagonal_one, Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]`. Conclude with `absurd (@h 0 1 rfl) (by decide)`.
-/
theorem not_reg_one : ¬ Reg (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rintro ⟨-, h⟩
  rw [nrm, theta_one, Matrix.mul_one, ← Matrix.diagonal_one, Matrix.charpoly_diagonal,
    Polynomial.separable_prod_X_sub_C_iff] at h
  exact absurd (@h 0 1 rfl) (by decide)

end GlobalTheory.Tw.Model
