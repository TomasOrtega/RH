import Mathlib
import Formalism.SatakeDualWeyl.StatementF
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOneAddPiOMul
import GroundTheory.LocalFields.FilteredSurj
open Polynomial Matrix Formalism.UG

namespace GlobalTheory.UTr

/- English proof (translation)
Introduce `R _ s n M hM`. Break down `subsingleton_or_nontrivial R with hR | hR` into its components or cases. Conclude with `⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩`. Use `set N := cT s M with hNdef`. Establish `hdeg : M.charpoly.natDegree = n` using `by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`.

Establish `hdegN : N.charpoly.natDegree = n` using `by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Establish `hmap : M.charpoly.map s = N.charpoly`. Rewrite using `[← Matrix.charpoly_map, ← Matrix.charpoly_transpose]`. Both sides reduce to the same expression. Establish `hrev : (M.charpoly.map s).reflect n = N.charpolyRev`.

Rewrite using `[hmap, ← Matrix.reverse_charpoly, Polynomial.reverse, hdegN]`. Establish `hdetN : N.det * M.det = 1` using `by rw [← Matrix.det_mul, hM, Matrix.det_one]`. Establish `hNd : N.det = s M.det`. Rewrite using `[hNdef, cT, Matrix.det_transpose, RingHom.map_det]`. Both sides reduce to the same expression.

Establish `h0 : M.charpoly.coeff 0 = (-1) ^ n * M.det`. Rewrite using `[Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]`. Establish `hs0 : s (M.charpoly.coeff 0) = (-1) ^ n * N.det`. Rewrite using `[h0, map_mul, map_pow, map_neg, map_one, hNd]`. Use `⟨Matrix.charpoly_monic M, ?_⟩` and prove the remaining obligations.

Rewrite using `[hdeg, hrev, Matrix.charpolyRev, hs0]`. Establish `hA : (1 - (X : R[X]) • N.map C) * M.map C = -charmatrix M`. Rewrite using `[sub_mul, one_mul, smul_mul_assoc, ← Matrix.map_mul, hM, Matrix.map_one _ (map_zero C) (map_one C), charmatrix, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply, neg_sub]`. Both sides reduce to the same expression. Establish `e1 : (1 - (X : R[X]) • N.map C).det * C M.det = (-1) ^ n * M.charpoly`.

Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_mul, hA, Matrix.det_neg, Fintype.card_fin]`. Both sides reduce to the same expression. Establish `e2 : C N.det * C M.det = (1 : R[X])` using `by rw [← C_mul, hdetN, C_1]`. Rewrite using `[C_mul, C_pow, C_neg, C_1]`. Take the linear combination `(-C N.det) * e1 + (1 - (X : R[X]) • N.map C).det * e2`.
-/
theorem isCsr_charpoly_of_cT_mul_eq_one : ∀ (R : Type) [CommRing R] (s : R →+* R) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) R), cT s M * M = 1 → GlobalTheory.UTr.IsCsr s M.charpoly := by
  intro R _ s n M hM
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  set N := cT s M with hNdef
  have hdeg : M.charpoly.natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hdegN : N.charpoly.natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hmap : M.charpoly.map s = N.charpoly := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_transpose]; rfl
  have hrev : (M.charpoly.map s).reflect n = N.charpolyRev := by
    rw [hmap, ← Matrix.reverse_charpoly, Polynomial.reverse, hdegN]
  have hdetN : N.det * M.det = 1 := by rw [← Matrix.det_mul, hM, Matrix.det_one]
  have hNd : N.det = s M.det := by
    rw [hNdef, cT, Matrix.det_transpose, RingHom.map_det]; rfl
  have h0 : M.charpoly.coeff 0 = (-1) ^ n * M.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
      one_pow, one_mul]
  have hs0 : s (M.charpoly.coeff 0) = (-1) ^ n * N.det := by
    rw [h0, map_mul, map_pow, map_neg, map_one, hNd]
  refine ⟨Matrix.charpoly_monic M, ?_⟩
  rw [hdeg, hrev, Matrix.charpolyRev, hs0]
  have hA : (1 - (X : R[X]) • N.map C) * M.map C = -charmatrix M := by
    rw [sub_mul, one_mul, smul_mul_assoc, ← Matrix.map_mul, hM, Matrix.map_one _ (map_zero C) (map_one C),
      charmatrix, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply, neg_sub]; rfl
  have e1 : (1 - (X : R[X]) • N.map C).det * C M.det = (-1) ^ n * M.charpoly := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_mul, hA, Matrix.det_neg, Fintype.card_fin]; rfl
  have e2 : C N.det * C M.det = (1 : R[X]) := by rw [← C_mul, hdetN, C_1]
  rw [C_mul, C_pow, C_neg, C_1]
  linear_combination (-C N.det) * e1 + (1 - (X : R[X]) • N.map C).det * e2

end GlobalTheory.UTr
