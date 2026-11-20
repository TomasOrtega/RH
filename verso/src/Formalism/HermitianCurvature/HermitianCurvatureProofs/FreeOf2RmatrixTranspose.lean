import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

namespace Formalism.FourierDecayAlt.P.Fr4

section

variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

/- English proof (translation)
Introduce `_ _` and use `Commute.one_right _`.
-/
theorem free_one (c : S) : FreeOf c (1 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.one_right _

/- English proof (translation)
Introduce `_ _` and use `Commute.zero_right _`.
-/
theorem free_zero (c : S) : FreeOf c (0 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.zero_right _

/- English proof (translation)
Introduce `i j` and use `(hx i j).mul_right (hy i j)`.
-/
theorem free_mul {c : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) : FreeOf c (x * y) :=
  fun i j => (hx i j).mul_right (hy i j)

/- English proof (translation)
Introduce `i j` and use `(hx i j).add_right (hy i j)`.
-/
theorem free_add {c : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) : FreeOf c (x + y) :=
  fun i j => (hx i j).add_right (hy i j)

/- English proof (translation)
Introduce `i j` and use `(hx i j).sub_right (hy i j)`.
-/
theorem free_sub {c : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) : FreeOf c (x - y) :=
  fun i j => (hx i j).sub_right (hy i j)

/- English proof (translation)
Introduce `i j` and use `(hx i j).neg_right`.
-/
theorem free_neg {c : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf c x) : FreeOf c (-x) :=
  fun i j => (hx i j).neg_right

/- English proof (translation)
Introduce `i j` and use `(hx i j).smul_right k`.
-/
theorem free_smul {c : S} {x : SlopeTestRemainingChoices S A} (k : ℂ) (hx : FreeOf c x) : FreeOf c (k • x) :=
  fun i j => (hx i j).smul_right k

/- English proof (translation)
Introduce `i j` and use `(hx i j).pow_right n`.
-/
theorem free_pow {c : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (n : ℕ) : FreeOf c (x ^ n) :=
  fun i j => (hx i j).pow_right n

/- English proof (translation)
Introduce `i j`. Establish `h` using `(hx j i).star_star`. Rewrite `h` using `[Wd1.star_eU]`. Then use the resulting hypothesis.
-/
theorem free_star [StarRing A] {c : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf c x) : FreeOf c (star x) := by
  intro i j
  have h := (hx j i).star_star
  rwa [Wd1.star_eU] at h

/- English proof (translation)
Introduce `i j`. Use `show (eU c i j : SlopeTestRemainingChoices S A) * io x = io x * eU c i j`. Use extensionality with `u v`. Unfold `io`. Rewrite using `[Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Wd1.eU_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem free_io (c : S) (x : A) : FreeOf c (io x : SlopeTestRemainingChoices S A) := by
  intro i j
  show (eU c i j : SlopeTestRemainingChoices S A) * io x = io x * eU c i j
  ext u v
  unfold io
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Wd1.eU_apply]
  split_ifs <;> simp

/- English proof (translation)
Introduce `i j` and use `Wd1.eU_comm_of_ne hc i j k l`.
-/
theorem free_eU {a c : S} (hc : c ≠ a) (k l : Fin 2) : FreeOf c (eU a k l : SlopeTestRemainingChoices S A) :=
  fun i j => Wd1.eU_comm_of_ne hc i j k l

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_two]`. Conclude with `free_add (free_mul (hM _ _) (hN _ _)) (free_mul (hM _ _) (hN _ _))`.
-/
theorem freeOf2_mul {c : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) (hN : FreeOf2 c N) : FreeOf2 c (M * N) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact free_add (free_mul (hM _ _) (hN _ _)) (free_mul (hM _ _) (hN _ _))

/- English proof (translation)
Introduce `i j` and use `hM j i`.
-/
theorem freeOf2_transpose {c : S} {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) : FreeOf2 c Mᵀ :=
  fun i j => hM j i

/- English proof (translation)
Introduce `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `hx`. Conclude with `hy`. Conclude with `hz`.

Conclude with `hw`.
-/
theorem freeOf2_matrix_entries {c : S} {x y z w : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) (hz : FreeOf c z)
    (hw : FreeOf c w) : FreeOf2 c !![x, y; z, w] := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact hx
  · exact hy
  · exact hz
  · exact hw

/- English proof (translation)
Introduce `i j`. Distinguish the cases in `h : i = j`. Rewrite using `[h, Matrix.one_apply_eq]`. Conclude with `free_one c`. Rewrite using `[Matrix.one_apply_ne h]`.

Conclude with `free_zero c`.
-/
theorem freeOf2_one (c : S) : FreeOf2 c (1 : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  by_cases h : i = j
  · rw [h, Matrix.one_apply_eq]; exact free_one c
  · rw [Matrix.one_apply_ne h]; exact free_zero c

/- English proof (translation)
Introduce `i j`. Unfold `Rh0`. Rewrite using `[Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply]`. Conclude with `free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc j i))`.
-/
theorem freeOf2_rmatrix {a c : S} (hc : c ≠ a) (D : ℂ) : FreeOf2 c (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  unfold Rh0
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc j i))

/- English proof (translation)
Introduce `i j`. Unfold `Rht0`. Rewrite using `[Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply]`. Conclude with `free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc i j))`.
-/
theorem freeOf2_rmatrix_transpose {a c : S} (hc : c ≠ a) (D : ℂ) : FreeOf2 c (Rht0 a D : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  unfold Rht0
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc i j))

/- English proof (translation)
Introduce `i j` and use `free_io c (M i j)`.
-/
theorem freeOf2_lift (c : S) (M : M2 A) : FreeOf2 c (lift0 M : M2 (SlopeTestRemainingChoices S A)) :=
  fun i j => free_io c (M i j)

/- English proof (translation)
Unfold `Formalism.YangianSpanCharacter.F.blk E1 Pf`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>`. Simplify using `[Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, mul_sub]`.
-/
theorem blk_plus (M : M2 (SlopeTestRemainingChoices S A)) (D : ℂ) (i j k l : Fin 2) :
    Formalism.YangianSpanCharacter.F.blk (E1 M *
      ((D - 1)⁻¹ • (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)))) i j k l =
      (D - 1)⁻¹ • (D • (if k = l then M i j else 0) - (if k = j then M i l else 0)) := by
  unfold Formalism.YangianSpanCharacter.F.blk E1 Pf
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, mul_sub]

/- English proof (translation)
Unfold `Formalism.YangianSpanCharacter.F.blk E1 Pf pt1`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>`. Simplify using `[Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, sub_mul]`.
-/
theorem blk_minus (M : M2 (SlopeTestRemainingChoices S A)) (d : ℂ) (i j k l : Fin 2) :
    Formalism.YangianSpanCharacter.F.blk (((d - 1)⁻¹ • pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A))) *
      E1 M) i j k l =
      (d - 1)⁻¹ • (d • (if k = l then M i j else 0) - (if i = k then M l j else 0)) := by
  unfold Formalism.YangianSpanCharacter.F.blk E1 Pf pt1
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, sub_mul]

/- English proof (translation)
Unfold `Rh0 P0`. Rewrite using `[Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_sub, Matrix.sub_apply, Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_one, Matrix.mul_apply, Fin.sum_univ_two]`. Both sides reduce to the same expression.
-/
theorem mul_rmatrix_apply (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (D : ℂ) (i j : Fin 2) :
    (M * Rh0 a D : M2 (SlopeTestRemainingChoices S A)) i j =
      (D - 1)⁻¹ • (D • M i j - (M i 0 * eU a j 0 + M i 1 * eU a j 1)) := by
  unfold Rh0 P0
  rw [Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_sub, Matrix.sub_apply, Matrix.mul_smul, Matrix.smul_apply,
    Matrix.mul_one, Matrix.mul_apply, Fin.sum_univ_two]
  rfl

/- English proof (translation)
Unfold `Rht0 Q0`. Rewrite using `[Matrix.smul_mul, Matrix.smul_apply, Matrix.sub_mul, Matrix.sub_apply, Matrix.smul_mul, Matrix.smul_apply, Matrix.one_mul, Matrix.mul_apply, Fin.sum_univ_two]`. Both sides reduce to the same expression.
-/
theorem Rht0_mul_apply (b : S) (M : M2 (SlopeTestRemainingChoices S A)) (d : ℂ) (i j : Fin 2) :
    (Rht0 b d * M : M2 (SlopeTestRemainingChoices S A)) i j =
      (d - 1)⁻¹ • (d • M i j - (eU b i 0 * M 0 j + eU b i 1 * M 1 j)) := by
  unfold Rht0 Q0
  rw [Matrix.smul_mul, Matrix.smul_apply, Matrix.sub_mul, Matrix.sub_apply, Matrix.smul_mul, Matrix.smul_apply,
    Matrix.one_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rfl

/- English proof (translation)
Establish `h1` using `Wd1.sum_eU_diag (A := A) a`. Rewrite `h1` using `[Fin.sum_univ_two]`. Establish `h2 : x = eU a 0 0 * x + eU a 1 1 * x` using `by rw [← add_mul, h1, one_mul]`. Unfold `ins`. Use `conv_rhs => rw [h2]`.

Apply the tactic sequence `fin_cases m <;>`. Simplify using `[Fin.sum_univ_two, mul_sub, smul_sub, smul_add]`.
-/
theorem ins_block (a : S) (c D : ℂ) (x : SlopeTestRemainingChoices S A) (y : Fin 2 → SlopeTestRemainingChoices S A) (m : Fin 2) :
    ins a (Matrix.of fun k l => c • (D • (if k = l then x else 0) - (if k = m then y l else 0))) =
      c • (D • x - (eU a m 0 * y 0 + eU a m 1 * y 1)) := by
  have h1 := Wd1.sum_eU_diag (A := A) a
  rw [Fin.sum_univ_two] at h1
  have h2 : x = eU a 0 0 * x + eU a 1 1 * x := by rw [← add_mul, h1, one_mul]
  unfold ins
  conv_rhs => rw [h2]
  fin_cases m <;>
    simp [Fin.sum_univ_two, mul_sub, smul_sub, smul_add]

end

section

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

/- English proof (translation)
The claim follows from `free_add (free_io c _) (free_mul (free_io c _) (h.2.2.2.2.2.2.2.2 Y))`.
-/
theorem free_l (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) (Y : ℂ) : FreeOf c (f.l L Y) :=
  free_add (free_io c _) (free_mul (free_io c _) (h.2.2.2.2.2.2.2.2 Y))

/- English proof (translation)
The claim follows from `free_mul (free_pow (free_io c _) _) h.2.2.2.2.2.2.1`.
-/
theorem free_d (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) : FreeOf c (f.d L) :=
  free_mul (free_pow (free_io c _) _) h.2.2.2.2.2.2.1

/- English proof (translation)
The claim follows from `free_mul h.2.2.2.2.2.2.2.1 (free_pow (free_io c _) _)`.
-/
theorem free_di (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) : FreeOf c (f.di L) :=
  free_mul h.2.2.2.2.2.2.2.1 (free_pow (free_io c _) _)

/- English proof (translation)
The claim follows from `free_mul (free_mul (free_di L h) (free_star (free_l L h _))) (free_d L h)`.
-/
theorem free_m (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) (Y : ℂ) : FreeOf c (f.m L Y) :=
  free_mul (free_mul (free_di L h) (free_star (free_l L h _))) (free_d L h)

/- English proof (translation)
The claim follows from `free_smul _ (free_sub (h.2.2.2.2.2.2.2.2 Y) (h.2.2.2.2.2.2.2.2 Ya))`.
-/
theorem free_DD {f : FrameData S A} {c : S} (h : f.Free c) (Y Ya : ℂ) : FreeOf c (f.DD Y Ya) :=
  free_smul _ (free_sub (h.2.2.2.2.2.2.2.2 Y) (h.2.2.2.2.2.2.2.2 Ya))

/- English proof (translation)
The claim follows from `free_io c _`.
-/
theorem free_tz (L : LevelData A r) (c : S) : FreeOf c (tz L : SlopeTestRemainingChoices S A) := free_io c _

/- English proof (translation)
Take `⟨hRR, hTT, hF, hFi, hx, hxi, hcc, hci, hee⟩` from `id h`. Establish `z` using `free_zero (A := A) c`. Establish `o` using `free_one (A := A) c`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `free_mul hRR (Wd1.ins_free hc _ (hTT Ya))`.

Conclude with `fun Y => freeOf2_mul (hTT Y) (freeOf2_rmatrix hc _)`. Conclude with `free_mul (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries (free_io c _) z z (free_io c _)) (freeOf2_matrix_entries o z (free_mul (free_io c _) (free_l L h Ya)) (free_io c _)))) hF`. Conclude with `free_mul hFi (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries o z (free_neg (free_l L h Ya)) (free_io c _)) (freeOf2_matrix_entries (free_io c _) z z (free_io c _))))`. Conclude with `fun Y => free_mul (hx Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))`. Conclude with `fun Y => free_mul (hxi Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))`.

Conclude with `free_mul hcc (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hxi _)) z z (hx _)))`. Conclude with `free_mul hci (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hx _)) z z (hxi _)))`. Conclude with `fun Y => Wd1.ins_free hc _ (freeOf2_matrix_entries (free_add (free_sub (hee Y) (free_DD h Y Ya)) (free_tz L c)) (free_neg (free_smul _ o)) z (free_mul (free_mul (hxi _) (hee Y)) (hx _)))`.
-/
theorem plus_free (L : LevelData A r) {f : FrameData S A} {a c : S} (hc : c ≠ a) (h : f.Free c) (Ya : ℂ) :
    (f.plus L a Ya).Free c := by
  obtain ⟨hRR, hTT, hF, hFi, hx, hxi, hcc, hci, hee⟩ := id h
  have z := free_zero (A := A) c
  have o := free_one (A := A) c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact free_mul hRR (Wd1.ins_free hc _ (hTT Ya))
  · exact fun Y => freeOf2_mul (hTT Y) (freeOf2_rmatrix hc _)
  · exact free_mul (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries (free_io c _) z z (free_io c _))
      (freeOf2_matrix_entries o z (free_mul (free_io c _) (free_l L h Ya)) (free_io c _)))) hF
  · exact free_mul hFi (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries o z (free_neg (free_l L h Ya)) (free_io c _))
      (freeOf2_matrix_entries (free_io c _) z z (free_io c _))))
  · exact fun Y => free_mul (hx Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact fun Y => free_mul (hxi Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact free_mul hcc (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hxi _)) z z (hx _)))
  · exact free_mul hci (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hx _)) z z (hxi _)))
  · exact fun Y => Wd1.ins_free hc _ (freeOf2_matrix_entries (free_add (free_sub (hee Y) (free_DD h Y Ya)) (free_tz L c))
      (free_neg (free_smul _ o)) z (free_mul (free_mul (hxi _) (hee Y)) (hx _)))

/- English proof (translation)
Take `⟨hRR, hTT, hF, hFi, hx, hxi, hcc, hci, hee⟩` from `id h`. Establish `z` using `free_zero (A := A) c`. Establish `o` using `free_one (A := A) c`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `free_mul hRR (Wd1.ins_free hc _ (freeOf2_transpose (hTT Yb)))`.

Conclude with `fun Y => freeOf2_mul (freeOf2_rmatrix_transpose hc _) (hTT Y)`. Conclude with `free_mul (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries (free_io c _) z z (free_io c _)) (freeOf2_matrix_entries o z (free_mul (free_io c _) (free_m L h Yb)) (free_io c _)))) hF`. Conclude with `free_mul hFi (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries o z (free_neg (free_m L h Yb)) (free_io c _)) (freeOf2_matrix_entries (free_io c _) z z (free_io c _))))`. Conclude with `fun Y => free_mul (hx Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))`. Conclude with `fun Y => free_mul (hxi Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))`.

Conclude with `free_mul hcc (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hxi _)) z z (hx _)))`. Conclude with `free_mul hci (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hx _)) z z (hxi _)))`. Conclude with `fun Y => Wd1.ins_free hc _ (freeOf2_matrix_entries (hee Y) z (free_neg (free_smul _ (free_mul (hxi _) (hxi _)))) (free_add (free_sub (free_mul (free_mul (hxi _) (hee Y)) (hx _)) (free_DD h Y Yb)) (free_tz L c)))`.
-/
theorem minus_free (L : LevelData A r) {f : FrameData S A} {b c : S} (hc : c ≠ b) (h : f.Free c) (Yb : ℂ) :
    (f.minus L b Yb).Free c := by
  obtain ⟨hRR, hTT, hF, hFi, hx, hxi, hcc, hci, hee⟩ := id h
  have z := free_zero (A := A) c
  have o := free_one (A := A) c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact free_mul hRR (Wd1.ins_free hc _ (freeOf2_transpose (hTT Yb)))
  · exact fun Y => freeOf2_mul (freeOf2_rmatrix_transpose hc _) (hTT Y)
  · exact free_mul (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries (free_io c _) z z (free_io c _))
      (freeOf2_matrix_entries o z (free_mul (free_io c _) (free_m L h Yb)) (free_io c _)))) hF
  · exact free_mul hFi (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries o z (free_neg (free_m L h Yb)) (free_io c _))
      (freeOf2_matrix_entries (free_io c _) z z (free_io c _))))
  · exact fun Y => free_mul (hx Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact fun Y => free_mul (hxi Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact free_mul hcc (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hxi _)) z z (hx _)))
  · exact free_mul hci (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hx _)) z z (hxi _)))
  · exact fun Y => Wd1.ins_free hc _ (freeOf2_matrix_entries (hee Y) z (free_neg (free_smul _ (free_mul (hxi _) (hxi _))))
      (free_add (free_sub (free_mul (free_mul (hxi _) (hee Y)) (hx _)) (free_DD h Y Yb)) (free_tz L c)))

/- English proof (translation)
Assemble the required witnesses or components as `⟨free_one c, fun _ => freeOf2_lift c _, free_one c, free_one c, fun _ => free_io c _, fun _ => free_io c _, free_one c, free_one c, fun _ => free_io c _⟩`.
-/
theorem start_free (st : Start A) (c : S) : (st.frame : FrameData S A).Free c :=
  ⟨free_one c, fun _ => freeOf2_lift c _, free_one c, free_one c, fun _ => free_io c _, fun _ => free_io c _,
    free_one c, free_one c, fun _ => free_io c _⟩

end

end Formalism.FourierDecayAlt.P.Fr4

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
Introduce `A S _ _ _ _ _ a M D hM i j`. Establish `e : Formalism.YangianSpanCharacter.F.blk (E1 M * ((D - 1)⁻¹ • (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)))) i j = Matrix.of fun k l => (D - 1)⁻¹ • (D • (if k = l then M i j else 0) - (if k = j then M i l …`. Use extensionality with `k l`. Conclude with `congrFun (congrFun (Fr4.blk_plus M D i j k l) _) _`. Rewrite using `[e, Fr4.ins_block a _ D (M i j) (fun l => M i l) j, Fr4.mul_rmatrix_apply, (hM i 0 j 0).eq, (hM i 1 j 1).eq]`.
-/
theorem position_block_plus_alt : Formalism.FourierDecayAlt.Fr.CoordinateBlockCondition := by
  intro A S _ _ _ _ _ a M D hM i j
  have e : Formalism.YangianSpanCharacter.F.blk (E1 M *
      ((D - 1)⁻¹ • (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)))) i j =
      Matrix.of fun k l => (D - 1)⁻¹ • (D • (if k = l then M i j else 0) - (if k = j then M i l else 0)) := by
    ext k l
    exact congrFun (congrFun (Fr4.blk_plus M D i j k l) _) _
  rw [e, Fr4.ins_block a _ D (M i j) (fun l => M i l) j, Fr4.mul_rmatrix_apply, (hM i 0 j 0).eq, (hM i 1 j 1).eq]

/- English proof (translation)
Introduce `A S _ _ _ _ _ b M d i j`. Establish `e : Formalism.YangianSpanCharacter.F.blk (((d - 1)⁻¹ • pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A))) * E1 M) i j = Matrix.of fun k l => (d - 1)⁻¹ • (d • (if k = l then M i j else 0) - (if k = i then M …`. Use extensionality with `k l`. Use `Fr4.blk_minus M d i j k l` as an intermediate fact. Simplify using `only [eq_comm (a := i) (b := k)] at this`.

Conclude with `congrFun (congrFun this _) _`. Rewrite using `[e, Fr4.ins_block b _ d (M i j) (fun l => M l j) i, Fr4.Rht0_mul_apply]`.
-/
theorem position_block_minus : Formalism.FourierDecayAlt.Fr.TransposedCoordinateBlockCondition := by
  intro A S _ _ _ _ _ b M d i j
  have e : Formalism.YangianSpanCharacter.F.blk (((d - 1)⁻¹ • pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) -
      Pf (SlopeTestRemainingChoices S A))) * E1 M) i j =
      Matrix.of fun k l => (d - 1)⁻¹ • (d • (if k = l then M i j else 0) - (if k = i then M l j else 0)) := by
    ext k l
    have := Fr4.blk_minus M d i j k l
    simp only [eq_comm (a := i) (b := k)] at this
    exact congrFun (congrFun this _) _
  rw [e, Fr4.ins_block b _ d (M i j) (fun l => M l j) i, Fr4.Rht0_mul_apply]

/- English proof (translation)
Introduce `A S _ _ _ _ _ _ r L st w c`. Proceed by induction on `w with`. Consider the case `nil => intro _`. Conclude with `Fr4.start_free st c`. Consider the case `cons l w ih`.

Introduce `hc`. Rewrite `hc` using `[List.map_cons, List.mem_cons, not_or]`. Establish `h` using `ih hc.2`. Use `show (if l.plus then (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt else (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt).Free c`. Use `split_ifs`.

Conclude with `Fr4.plus_free L hc.1 h l.pt`. Conclude with `Fr4.minus_free L hc.1 h l.pt`.
-/
theorem frame_free_of_new_position : Formalism.FourierDecayAlt.Fr.FrameFree := by
  intro A S _ _ _ _ _ _ r L st w c
  induction w with
  | nil => intro _; exact Fr4.start_free st c
  | cons l w ih =>
    intro hc
    rw [List.map_cons, List.mem_cons, not_or] at hc
    have h := ih hc.2
    show (if l.plus then (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt else (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt).Free c
    split_ifs
    · exact Fr4.plus_free L hc.1 h l.pt
    · exact Fr4.minus_free L hc.1 h l.pt

end Formalism.FourierDecayAlt.P
