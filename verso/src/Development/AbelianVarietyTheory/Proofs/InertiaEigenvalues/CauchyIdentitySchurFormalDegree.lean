import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurMulDetEqDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacobiTrudiAlternantExpansionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurPolynomialPadZerosEqJacobiTrudiDeterminantStatement

noncomputable section

open MvPolynomial

namespace GlobalTheory.JSW.CauchyGlue

/- English proof (translation)
Rewrite using `[jtDet, jtDet, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_jtDet {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (m : ℕ) (h : ℕ → A)
    (l : Fin m → ℕ) : f (jtDet m h l) = jtDet m (fun k => f (h k)) l := by
  rw [jtDet, jtDet, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[alternant, alternant, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_alternant {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (m : ℕ) (μ : Fin m → ℕ) :
    MvPolynomial.map f (alternant A m μ) = alternant B m μ := by
  rw [alternant, alternant, RingHom.map_det]
  congr 1
  ext i j
  simp

/- English proof (translation)
Rewrite using `[alternant, ← Matrix.det_transpose]`. Both sides reduce to the same expression.
-/
theorem alternant_eq_det (A : Type*) [CommRing A] (m : ℕ) (μ : Fin m → ℕ) :
    alternant A m μ = Matrix.det (Matrix.of fun i j : Fin m => (X i : MvPolynomial (Fin m) A) ^ μ j) := by
  rw [alternant, ← Matrix.det_transpose]
  rfl

/- English proof (translation)
Establish `e : (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℂ) ^ staircase m i) = (Matrix.transpose (Matrix.vandermonde (fun j : Fin m => (X j : MvPolynomial (Fin m) ℂ)))).submatrix Fin.revPerm id`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.vandermonde_apply, Fin.revPerm_apply, id, staircase, Fin.val_rev]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[alternant, e, Matrix.det_permute, Matrix.det_transpose]`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m))) with h | h <;> simp [h]`. Conclude with `(Matrix.det_vandermonde_ne_zero_iff).2 (MvPolynomial.X_injective)`.
-/
theorem alternant_staircase_ne_zero (m : ℕ) : alternant ℂ m (staircase m) ≠ 0 := by
  have e : (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℂ) ^ staircase m i) =
      (Matrix.transpose (Matrix.vandermonde (fun j : Fin m => (X j : MvPolynomial (Fin m) ℂ)))).submatrix Fin.revPerm id := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Fin.revPerm_apply, id, staircase, Fin.val_rev]
    congr 1
    omega
  rw [alternant, e, Matrix.det_permute, Matrix.det_transpose]
  refine mul_ne_zero ?_ ?_
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m))) with h | h <;> simp [h]
  · exact (Matrix.det_vandermonde_ne_zero_iff).2 (MvPolynomial.X_injective)

/- English proof (translation)
Simplify using `only [alternant_eq_det, staircase]`. Rewrite using `[schur_mul_det_eq_det m l hl]`. Use `congr 1`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply]`.

Use `congr 1`. Use `j.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem bialt_int (m : ℕ) (l : Fin m → ℕ) (hl : Antitone l) :
    schur m l * alternant ℤ m (staircase m) = alternant ℤ m (fun i => l i + staircase m i) := by
  simp only [alternant_eq_det, staircase]
  rw [schur_mul_det_eq_det m l hl]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.of_apply]
  congr 1
  have := j.2
  omega

/- English proof (translation)
Introduce `m n hmn α β d`. Use `set hC : ℕ → ℂ := fun k => eval₂ (Int.castRingHom ℂ) α (hsymm (Fin n) ℤ k) with hhC`. Establish `hA` using `GlobalTheory.T.jacobi_trudi_alternant_expansion (A := ℂ) m d hC`. Establish `hpad : ∀ l : Fin m → ℕ, schurAt (padTo hmn l) α = jtDet m hC l`. Introduce `l`.

Rewrite using `[schurAt, GlobalTheory.T.schurPolynomial_padZeros_eq_jacobiTrudiDeterminant hmn l, ← MvPolynomial.coe_eval₂Hom, map_jtDet]`. Both sides reduce to the same expression. Establish `hbi : ∀ l ∈ antiParts m d, alternant ℂ m (fun i => l i + staircase m i) = MvPolynomial.map (Int.castRingHom ℂ) (schur m l) * alternant ℂ m (staircase m)`. Introduce `l hl`. Use `congrArg (MvPolynomial.map (Int.castRingHom ℂ)) (bialt_int m l (mem_antiParts.1 hl).2)` as an intermediate fact.

Rewrite `this` using `[map_mul, map_alternant, map_alternant]`. Conclude with `this.symm`. Establish `hR : ∑ l ∈ antiParts m d, C (jtDet m hC l) * alternant ℂ m (fun i => l i + staircase m i) = alternant ℂ m (staircase m) * ∑ l ∈ antiParts m d, C (jtDet m hC l) * MvPolynomial.map (Int.castRingHom ℂ) (schur m l)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations.

Rewrite using `[hbi l hl]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hA` using `[hR]`. Establish `hP` using `mul_left_cancel₀ (alternant_staircase_ne_zero m) hA`. Establish `hE` using `congrArg (MvPolynomial.eval β) hP`.

Simplify using `only [map_sum, map_prod, map_mul, eval_C, eval_X, map_pow, MvPolynomial.eval_map] at hE`. Use `(Finset.sum_congr rfl fun l _ => ?_).trans hE.symm` and prove the remaining obligations. Rewrite using `[hpad]`. Both sides reduce to the same expression.
-/
theorem cauchy_formal : ∀ {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (d : ℕ),
    ∑ l ∈ GlobalTheory.JSW.antiParts m d, GlobalTheory.JSW.schurAt (GlobalTheory.JSW.padTo hmn l) α * GlobalTheory.JSW.schurAt l β =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
  intro m n hmn α β d
  set hC : ℕ → ℂ := fun k => eval₂ (Int.castRingHom ℂ) α (hsymm (Fin n) ℤ k) with hhC
  have hA := GlobalTheory.T.jacobi_trudi_alternant_expansion (A := ℂ) m d hC
  have hpad : ∀ l : Fin m → ℕ, schurAt (padTo hmn l) α = jtDet m hC l := by
    intro l
    rw [schurAt, GlobalTheory.T.schurPolynomial_padZeros_eq_jacobiTrudiDeterminant hmn l, ← MvPolynomial.coe_eval₂Hom, map_jtDet]
    rfl
  have hbi : ∀ l ∈ antiParts m d, alternant ℂ m (fun i => l i + staircase m i) =
      MvPolynomial.map (Int.castRingHom ℂ) (schur m l) * alternant ℂ m (staircase m) := by
    intro l hl
    have := congrArg (MvPolynomial.map (Int.castRingHom ℂ)) (bialt_int m l (mem_antiParts.1 hl).2)
    rw [map_mul, map_alternant, map_alternant] at this
    exact this.symm
  have hR : ∑ l ∈ antiParts m d, C (jtDet m hC l) * alternant ℂ m (fun i => l i + staircase m i) =
      alternant ℂ m (staircase m) *
        ∑ l ∈ antiParts m d, C (jtDet m hC l) * MvPolynomial.map (Int.castRingHom ℂ) (schur m l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [hbi l hl]
    ring
  rw [hR] at hA
  have hP := mul_left_cancel₀ (alternant_staircase_ne_zero m) hA
  have hE := congrArg (MvPolynomial.eval β) hP
  simp only [map_sum, map_prod, map_mul, eval_C, eval_X, map_pow, MvPolynomial.eval_map] at hE
  refine (Finset.sum_congr rfl fun l _ => ?_).trans hE.symm
  rw [hpad]
  rfl

end GlobalTheory.JSW.CauchyGlue
