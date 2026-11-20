import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

open Finset MvPolynomial UpperTheory.Gal.Schur

namespace UpperTheory.Gal.Schur

/- English proof (translation)
Unfold `vdm`. Use `Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_` and prove the remaining obligations. Conclude with `sub_ne_zero.2 (MvPolynomial.X_injective.ne (Finset.mem_Ioi.1 hj).ne)`.
-/
private lemma vdm_X_ne (n : ℕ) : vdm (X : Fin n → MvPolynomial (Fin n) ℚ) ≠ 0 := by
  unfold vdm
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  exact sub_ne_zero.2 (MvPolynomial.X_injective.ne (Finset.mem_Ioi.1 hj).ne)

/- English proof (translation)
Unfold `sch`. Rewrite using `[MvPolynomial.aeval_X_left_apply]`.
-/
private lemma aeval_sch {R : Type} [CommRing R] [Algebra ℚ R] {n : ℕ} (lam : Fin n → ℕ)
    (g : Fin n → R) :
    aeval g (sch lam (X : Fin n → MvPolynomial (Fin n) ℚ)) = sch lam g := by
  unfold sch
  rw [MvPolynomial.aeval_X_left_apply]

/- English proof (translation)
Establish `h` using `GroundTheory.Heights₂.Heights.RestTerms.Schur.det_pow_staircase_eq_vandermondeOf g`. Establish `h' : vdm g = GroundTheory.Heights₂.Heights.RestTerms.vandermondeOf g` using `rfl`. Unfold `altn`. Rewrite using `[h']`. Simplify `h` using `[shift]`.
-/
private lemma altn_zero {R : Type} [CommRing R] {n : ℕ} (g : Fin n → R) :
    altn (shift fun _ => 0) g = vdm g := by
  have h := GroundTheory.Heights₂.Heights.RestTerms.Schur.det_pow_staircase_eq_vandermondeOf g
  have h' : vdm g = GroundTheory.Heights₂.Heights.RestTerms.vandermondeOf g := rfl
  unfold altn
  rw [h']
  simpa [shift] using h

/- English proof (translation)
Unfold `altn`. Establish `h : (Matrix.of fun i j : Fin n => g j ^ (shift (fun i => lam i + m)) i) = Matrix.of fun i j : Fin n => g j ^ m * (Matrix.of fun i j : Fin n => g j ^ (shift lam) i) i j`. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, shift]`. Rewrite using `[← pow_add]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h, Matrix.det_mul_row, Finset.prod_pow]`.
-/
private lemma altn_add {R : Type} [CommRing R] {n : ℕ} (lam : Fin n → ℕ) (m : ℕ) (g : Fin n → R) :
    altn (shift fun i => lam i + m) g = (∏ k, g k) ^ m * altn (shift lam) g := by
  unfold altn
  have h : (Matrix.of fun i j : Fin n => g j ^ (shift (fun i => lam i + m)) i) =
      Matrix.of fun i j : Fin n =>
        g j ^ m * (Matrix.of fun i j : Fin n => g j ^ (shift lam) i) i j := by
    ext i j
    simp only [Matrix.of_apply, shift]
    rw [← pow_add]
    congr 1
    omega
  rw [h, Matrix.det_mul_row, Finset.prod_pow]

/- English proof (translation)
Establish `h` using `tie (MvPolynomial (Fin n) ℚ) n (fun _ => 0) X`. Rewrite `h` using `[altn_zero]`. Conclude with `mul_right_cancel₀ (vdm_X_ne n) (h.trans (one_mul _).symm)`.
-/
private lemma sch_zero_X (tie : Comparison₂) (n : ℕ) :
    sch (fun _ => 0) (X : Fin n → MvPolynomial (Fin n) ℚ) = 1 := by
  have h := tie (MvPolynomial (Fin n) ℚ) n (fun _ => 0) X
  rw [altn_zero] at h
  exact mul_right_cancel₀ (vdm_X_ne n) (h.trans (one_mul _).symm)

/- English proof (translation)
Establish `h` using `tie (MvPolynomial (Fin n) ℚ) n (fun i => lam i + m) X`. Rewrite `h` using `[altn_add, ← tie (MvPolynomial (Fin n) ℚ) n lam X, ← mul_assoc]`. Conclude with `mul_right_cancel₀ (vdm_X_ne n) h`.
-/
private lemma sch_add_X (tie : Comparison₂) (n : ℕ) (lam : Fin n → ℕ) (m : ℕ) :
    sch (fun i => lam i + m) (X : Fin n → MvPolynomial (Fin n) ℚ) =
      (∏ k, (X k : MvPolynomial (Fin n) ℚ)) ^ m * sch lam X := by
  have h := tie (MvPolynomial (Fin n) ℚ) n (fun i => lam i + m) X
  rw [altn_add, ← tie (MvPolynomial (Fin n) ℚ) n lam X, ← mul_assoc] at h
  exact mul_right_cancel₀ (vdm_X_ne n) h

/- English proof (translation)
Introduce `tie R _ _ n g`. Use `⟨?_, fun lam m => ?_⟩` and prove the remaining obligations. Rewrite using `[← aeval_sch, sch_zero_X tie, map_one]`. Rewrite using `[← aeval_sch, sch_add_X tie, map_mul, map_pow, map_prod, aeval_sch]`. Simplify using `only [aeval_X]`.
-/
theorem schurDet_of :
    Comparison₂ → SchurDet := by
  intro tie R _ _ n g
  refine ⟨?_, fun lam m => ?_⟩
  · rw [← aeval_sch, sch_zero_X tie, map_one]
  · rw [← aeval_sch, sch_add_X tie, map_mul, map_pow, map_prod, aeval_sch]
    simp only [aeval_X]

end UpperTheory.Gal.Schur
