import Formalism.HermitianCurvature.OperatorsCommuteTranslations

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3

/- English proof (translation)
Establish `h1 : s * (s - 1) / 2 * 2 = s * (s - 1)` using `Nat.div_mul_cancel (Nat.even_mul_pred_self s).two_dvd`. Establish `h2 : (s + 1) * (s + 1 - 1) / 2 * 2 = (s + 1) * (s + 1 - 1)` using `Nat.div_mul_cancel (Nat.even_mul_pred_self (s + 1)).two_dvd`. Establish `h3 : s * (s - 1) + (s + 1) * (s + 1 - 1) = 2 * (s * s)`. Consider the cases of `s with`. Consider the case `zero => simp`.

Consider the case `succ n => simp only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Generalize the expression as in `s * (s - 1) = A at *`. Generalize the expression as in `(s + 1) * (s + 1 - 1) = B at *`. Generalize the expression as in `s * s = C at *`.

Use linear arithmetic over natural numbers and integers.
-/
theorem sgn_step (s : ℕ) : s * (s - 1) / 2 + (s + 1) * (s + 1 - 1) / 2 = s * s := by
  have h1 : s * (s - 1) / 2 * 2 = s * (s - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self s).two_dvd
  have h2 : (s + 1) * (s + 1 - 1) / 2 * 2 = (s + 1) * (s + 1 - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self (s + 1)).two_dvd
  have h3 : s * (s - 1) + (s + 1) * (s + 1 - 1) = 2 * (s * s) := by
    cases s with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  generalize s * (s - 1) = A at *
  generalize (s + 1) * (s + 1 - 1) = B at *
  generalize s * s = C at *
  omega

/- English proof (translation)
Establish `h1 : s * (s - 1) / 2 * 2 = s * (s - 1)` using `Nat.div_mul_cancel (Nat.even_mul_pred_self s).two_dvd`. Establish `h2 : (s + 2) * (s + 2 - 1) / 2 * 2 = (s + 2) * (s + 2 - 1)` using `Nat.div_mul_cancel (Nat.even_mul_pred_self (s + 2)).two_dvd`. Establish `h3 : s * (s - 1) + (s + 2) * (s + 2 - 1) = 2 * (s * (s + 1) + 1)`. Consider the cases of `s with`. Consider the case `zero => simp`.

Consider the case `succ n => simp only [Nat.add_sub_cancel, show n + 1 + 2 - 1 = n + 2 by omega]; ring`. Generalize the expression as in `s * (s - 1) = A at *`. Generalize the expression as in `(s + 2) * (s + 2 - 1) = B at *`. Generalize the expression as in `s * (s + 1) = C at *`. Use linear arithmetic over natural numbers and integers.
-/
theorem sgn_step2 (s : ℕ) : s * (s - 1) / 2 + (s + 2) * (s + 2 - 1) / 2 = s * (s + 1) + 1 := by
  have h1 : s * (s - 1) / 2 * 2 = s * (s - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self s).two_dvd
  have h2 : (s + 2) * (s + 2 - 1) / 2 * 2 = (s + 2) * (s + 2 - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self (s + 2)).two_dvd
  have h3 : s * (s - 1) + (s + 2) * (s + 2 - 1) = 2 * (s * (s + 1) + 1) := by
    cases s with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel, show n + 1 + 2 - 1 = n + 2 by omega]; ring
  generalize s * (s - 1) = A at *
  generalize (s + 2) * (s + 2 - 1) = B at *
  generalize s * (s + 1) = C at *
  omega

/- English proof (translation)
Break down `Nat.even_or_odd s with h | h` into its components or cases. Rewrite using `[Even.neg_one_pow h, Even.neg_one_pow (h.mul_left s)]`. Rewrite using `[Odd.neg_one_pow h, Odd.neg_one_pow (h.mul h)]`.
-/
theorem neg_one_pow_sq (s : ℕ) : (-1 : ℂ) ^ (s * s) = (-1) ^ s := by
  rcases Nat.even_or_odd s with h | h
  · rw [Even.neg_one_pow h, Even.neg_one_pow (h.mul_left s)]
  · rw [Odd.neg_one_pow h, Odd.neg_one_pow (h.mul h)]

/- English proof (translation)
Introduce `s`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `sgnW`. Rewrite using `[← pow_add, sgn_step, neg_one_pow_sq]`. Unfold `sgnW`.

Rewrite using `[← pow_add, sgn_step2, pow_succ, Even.neg_one_pow (Nat.even_mul_succ_self s)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sign_permutation_identity : SignE := by
  intro s
  refine ⟨?_, ?_⟩
  · unfold sgnW; rw [← pow_add, sgn_step, neg_one_pow_sq]
  · unfold sgnW; rw [← pow_add, sgn_step2, pow_succ, Even.neg_one_pow (Nat.even_mul_succ_self s)]; ring

/- English proof (translation)
Establish `h` using `(sign_permutation_identity m).1`. Establish `hsq : sgnW m * sgnW m = 1`. Unfold `sgnW`. Rewrite using `[← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem sgnW_succ (m : ℕ) : sgnW (m + 1) = (-1) ^ m * sgnW m := by
  have h := (sign_permutation_identity m).1
  have hsq : sgnW m * sgnW m = 1 := by
    unfold sgnW; rw [← pow_add, ← two_mul, pow_mul]; simp
  calc sgnW (m + 1) = (sgnW m * sgnW m) * sgnW (m + 1) := by rw [hsq, one_mul]
    _ = sgnW m * (sgnW m * sgnW (m + 1)) := by ring
    _ = (-1) ^ m * sgnW m := by rw [h]; ring

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp [sgnW]`. Consider the case `succ m ih`. Rewrite using `[Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last m)]`.

Establish `hsub : ((Matrix.of fun a b : Fin (m + 1) => if a.val + b.val + 1 = m + 1 then (1 : ℂ) else 0).submatrix Fin.succ (Fin.last m).succAbove) = Matrix.of fun a b : Fin m => if a.val + b.val + 1 = m then (1 : ℂ) else 0`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last, Fin.val_succ, Fin.val_castSucc]`. Use `congr 1`. Apply `propext` to reduce the goal to its premises.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hsub, ih, sgnW_succ]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Establish `hne : (j : ℕ) ≠ m` using `by intro h; apply hj; ext; simp [h]`.

Simplify using `[hne]`. Simplify using the standard rewrite rules.
-/
theorem antidiagonal_determinant : AntiDiagDet := by
  intro m
  induction m with
  | zero => simp [sgnW]
  | succ m ih =>
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last m)]
    · have hsub : ((Matrix.of fun a b : Fin (m + 1) => if a.val + b.val + 1 = m + 1 then (1 : ℂ) else 0).submatrix
          Fin.succ (Fin.last m).succAbove) =
          Matrix.of fun a b : Fin m => if a.val + b.val + 1 = m then (1 : ℂ) else 0 := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last, Fin.val_succ, Fin.val_castSucc]
        congr 1
        apply propext; omega
      rw [hsub, ih, sgnW_succ]
      simp
    · intro j _ hj
      have hne : (j : ℕ) ≠ m := by intro h; apply hj; ext; simp [h]
      simp [hne]
    · simp

end Formalism.FourierDecayAlt.P.SignAntidiagonal
