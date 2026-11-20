import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IpLEqZeroOfMemSpan

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.REAL

noncomputable section

namespace GlobalTheory.NilCov

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Rewrite using `[ipL_apply]`. Simplify using `only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]`.
-/
private theorem hs_eq_ipL (X : Matrix (Fin n) (Fin n) ℂ) : hs X = ipL X X := by
  rw [ipL_apply]
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _`.
-/
private theorem hs_nonneg' (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/- English proof (translation)
Establish `key : ∀ i j, ‖∑ k, A i k * B k j‖ ^ 2 ≤ (∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖B k j‖ ^ 2`. Introduce `i j`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))`. Use `_ ≤ (∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖B k j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _`.

Simplify using `only [Formalism.REAL.hs, Matrix.mul_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm`. Use `_ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * ∑ k, ∑ j, ‖B k j‖ ^ 2 := by congr 1; exact Finset.sum_comm`.
-/
private theorem hs_mul_le (A B : Matrix (Fin n) (Fin n) ℂ) : hs (A * B) ≤ hs A * hs B := by

  have key : ∀ i j, ‖∑ k, A i k * B k j‖ ^ 2 ≤ (∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖B k j‖ ^ 2 := by
    intro i j
    calc ‖∑ k, A i k * B k j‖ ^ 2 ≤ (∑ k, ‖A i k‖ * ‖B k j‖) ^ 2 := by
          gcongr
          exact (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
      _ ≤ (∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖B k j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  simp only [Formalism.REAL.hs, Matrix.mul_apply]
  calc ∑ i, ∑ j, ‖∑ k, A i k * B k j‖ ^ 2
        ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖B k j‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * ∑ j, ∑ k, ‖B k j‖ ^ 2 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * ∑ k, ∑ j, ‖B k j‖ ^ 2 := by congr 1; exact Finset.sum_comm

/- English proof (translation)
Simplify using `only [Formalism.REAL.hs, Matrix.neg_apply, norm_neg]`.
-/
private theorem hs_neg' (X : Matrix (Fin n) (Fin n) ℂ) : hs (-X) = hs X := by
  simp only [Formalism.REAL.hs, Matrix.neg_apply, norm_neg]

/- English proof (translation)
Establish `hsign : ∀ a, ‖(if ε a then (1 : ℂ) else -1)‖ = 1`. Apply the tactic sequence `intro a; split_ifs <;> simp`. Simplify using `only [Formalism.REAL.hs, Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, norm_mul, norm_star, hsign, one_mul, mul_one]`. Conclude with `Finset.sum_comm`.
-/
private theorem hs_inv_eq (X : Matrix (Fin n) (Fin n) ℂ) : hs (Jm ε * Xᴴ * Jm ε) = hs X := by

  have hsign : ∀ a, ‖(if ε a then (1 : ℂ) else -1)‖ = 1 := by
    intro a; split_ifs <;> simp
  simp only [Formalism.REAL.hs, Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.conjTranspose_apply, norm_mul, norm_star, hsign, one_mul, mul_one]
  exact Finset.sum_comm

/- English proof (translation)
Simplify using `only [Formalism.REAL.hs, Matrix.sub_apply, Matrix.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h` using `parallelogram_law_with_norm ℝ (X i j) (Y i j)`. Rewrite using `[sq, sq, sq, sq]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem hs_sub_add_hs_add_eq_parallelogram (X Y : Matrix (Fin n) (Fin n) ℂ) :
    hs (X - Y) + hs (X + Y) = 2 * hs X + 2 * hs Y := by
  simp only [Formalism.REAL.hs, Matrix.sub_apply, Matrix.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := parallelogram_law_with_norm ℝ (X i j) (Y i j)
  rw [sq, sq, sq, sq]
  linarith

/- English proof (translation)
Use `set X := uMat g - 1 with hXdef`. Use `set Y := Jm ε * Xᴴ * Jm ε with hYdef`. Establish `hc : ∀ i, ipL (E i) (X - Y) = 2 * ((X * (E i)ᴴ).trace).re`. Introduce `i`. Rewrite using `[ipL_sub_inv (hG i) X, ipL_apply]`.

Establish `hexp : X - Y = ∑ i, ipL (E i) (X - Y) • E i` using `eq_sum_of_mem_span hE hsp`. Establish `hD : hs (X - Y) = 4 * ∑ i, ((X * (E i)ᴴ).trace).re ^ 2`. Establish `h1 : ipL (X - Y) (X - Y) = ∑ i, ipL (E i) (X - Y) * ipL (E i) (X - Y)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sum]`.

Simplify using `only [map_smul, smul_eq_mul]`. Use `_ = ∑ i, ipL (E i) (X - Y) * ipL (E i) (X - Y) := Finset.sum_congr rfl fun i _ => by rw [ipL_comm (E i) (X - Y)]`. Rewrite using `[hs_eq_ipL, h1, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hc i]; ring`. Establish `hS : hs (X + Y) ≤ hs X ^ 2`.

Establish `hYX : X + Y = -(Y * X)` using `add_inv_eq g`. Establish `hYn : hs Y = hs X` using `hs_inv_eq X`. Rewrite using `[hYX, hs_neg', sq]`. Combine the equalities or inequalities in the displayed calculation. Establish `hpara` using `hs_sub_add_hs_add_eq_parallelogram X Y`.

Establish `hYn : hs Y = hs X` using `hs_inv_eq X`. Establish `hnn : 0 ≤ hs (X + Y)` using `hs_nonneg' _`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem sum_coord_sq_le_hs_and_hs_le (n d : ℕ) (ε : Fin n → Bool) (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) (hG : ∀ i, inG ε (E i)) (g : UJ ε)
    (hsp : (uMat g - 1) - Jm ε * (uMat g - 1)ᴴ * Jm ε ∈ Submodule.span ℝ (Set.range E)) :
    ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 ≤ hs (uMat g - 1) ∧
      hs (uMat g - 1) ≤ ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 + hs (uMat g - 1) ^ 2 / 4 := by
  set X := uMat g - 1 with hXdef
  set Y := Jm ε * Xᴴ * Jm ε with hYdef

  have hc : ∀ i, ipL (E i) (X - Y) = 2 * ((X * (E i)ᴴ).trace).re := by
    intro i
    rw [ipL_sub_inv (hG i) X, ipL_apply]
  have hexp : X - Y = ∑ i, ipL (E i) (X - Y) • E i := eq_sum_of_mem_span hE hsp

  have hD : hs (X - Y) = 4 * ∑ i, ((X * (E i)ᴴ).trace).re ^ 2 := by
    have h1 : ipL (X - Y) (X - Y) = ∑ i, ipL (E i) (X - Y) * ipL (E i) (X - Y) := by
      calc ipL (X - Y) (X - Y) = ipL (X - Y) (∑ i, ipL (E i) (X - Y) • E i) :=
            congrArg (fun Z => ipL (X - Y) Z) hexp
        _ = ∑ i, ipL (E i) (X - Y) * ipL (X - Y) (E i) := by
            rw [map_sum]
            simp only [map_smul, smul_eq_mul]
        _ = ∑ i, ipL (E i) (X - Y) * ipL (E i) (X - Y) :=
            Finset.sum_congr rfl fun i _ => by rw [ipL_comm (E i) (X - Y)]
    rw [hs_eq_ipL, h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hc i]; ring

  have hS : hs (X + Y) ≤ hs X ^ 2 := by
    have hYX : X + Y = -(Y * X) := add_inv_eq g
    have hYn : hs Y = hs X := hs_inv_eq X
    rw [hYX, hs_neg', sq]
    calc hs (Y * X) ≤ hs Y * hs X := hs_mul_le Y X
      _ = hs X * hs X := by rw [hYn]
  have hpara := hs_sub_add_hs_add_eq_parallelogram X Y
  have hYn : hs Y = hs X := hs_inv_eq X
  have hnn : 0 ≤ hs (X + Y) := hs_nonneg' _
  constructor <;> linarith

end GlobalTheory.NilCov
