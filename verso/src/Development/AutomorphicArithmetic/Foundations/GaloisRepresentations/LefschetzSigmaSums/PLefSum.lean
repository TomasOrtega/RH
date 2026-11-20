import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi

set_option autoImplicit false

noncomputable section

open Matrix Polynomial
open UpperTheory.Gal.W2 (lefTerm)

namespace UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Introduce `d A y`. Use `set p : ℂ[X] := (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X])).det with hp`. Establish `hdeg : p.natDegree < d + 1`. Establish `h1 : (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X]) : Matrix (Fin d) (Fin d) ℂ[X]) = (X : ℂ[X]) • A.map C + (1 : Matrix (Fin d) (Fin d) ℂ).map C`. Rewrite using `[Matrix.map_one C (map_zero _) (map_one _), add_comm]`.

Establish `hle` using `natDegree_det_X_add_C_le A 1`. Rewrite `hle` using `[← h1, Fintype.card_fin]`. Conclude with `Nat.lt_succ_of_le hle`. Establish `hev : p.eval (-y) = (1 - y • A).det`. Rewrite using `[hp, ← coe_evalRingHom, RingHom.map_det]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, coe_evalRingHom, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp <;> ring`. Unfold `lefTerm`.

Rewrite using `[← hev, eval_eq_sum_range' hdeg, Finset.sum_div]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lefSum_of : LefSum := by
  intro d A y
  set p : ℂ[X] := (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X])).det with hp
  have hdeg : p.natDegree < d + 1 := by
    have h1 : (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X]) : Matrix (Fin d) (Fin d) ℂ[X]) =
        (X : ℂ[X]) • A.map C + (1 : Matrix (Fin d) (Fin d) ℂ).map C := by
      rw [Matrix.map_one C (map_zero _) (map_one _), add_comm]
    have hle := natDegree_det_X_add_C_le A 1
    rw [← h1, Fintype.card_fin] at hle
    exact Nat.lt_succ_of_le hle
  have hev : p.eval (-y) = (1 - y • A).det := by
    rw [hp, ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply, coe_evalRingHom, smul_eq_mul]
    split_ifs <;> simp <;> ring
  unfold lefTerm
  rw [← hev, eval_eq_sum_range' hdeg, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end UpperTheory.Gal.LocalSmoothExtension
