import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

open Finset MvPolynomial UpperTheory.Gal.Schur

/- English proof (translation)
Introduce `R _ _ n lam g`. Establish `h` using `congrArg (aeval g) (GroundTheory.Heights₂.Heights.RestTerms.Schur.det_pow_add_staircase_eq lam)`. Rewrite `h` using `[AlgHom.map_det, map_mul]`. Establish `hM : ((Matrix.of fun i j => (X j : MvPolynomial (Fin n) ℚ) ^ (lam i + (n - 1 - (i : ℕ)))).map (aeval g)) = Matrix.of fun i j => g j ^ (lam i + (n - 1 - (i : ℕ)))`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Simplify using `[AlgHom.mapMatrix_apply, GroundTheory.Heights₂.Heights.RestTerms.vandermondeOf, map_prod, hM] at h`. Simplify `h.symm` using `[sch, vdm, altn, shift]`.
-/
theorem UpperTheory.Gal.Schur.tie :
    Comparison₂ := by
  intro R _ _ n lam g
  have h := congrArg (aeval g) (GroundTheory.Heights₂.Heights.RestTerms.Schur.det_pow_add_staircase_eq lam)
  rw [AlgHom.map_det, map_mul] at h
  have hM : ((Matrix.of fun i j => (X j : MvPolynomial (Fin n) ℚ) ^ (lam i + (n - 1 - (i : ℕ)))).map
      (aeval g)) = Matrix.of fun i j => g j ^ (lam i + (n - 1 - (i : ℕ))) := by
    ext i j
    simp
  simp [AlgHom.mapMatrix_apply, GroundTheory.Heights₂.Heights.RestTerms.vandermondeOf, map_prod, hM] at h
  simpa [sch, vdm, altn, shift] using h.symm
