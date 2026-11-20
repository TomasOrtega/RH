import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParamCommF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

/- English proof (translation)
Use `split_ifs with h`. Rewrite using `[Equiv.symm_apply_eq]`. Use `ext`. Simplify using the standard rewrite rules. Rewrite using `[Equiv.symm_apply_eq]`.

Use `ext`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem fsym (m n : ℕ) (i : Fin (m + n)) : finSumFinEquiv.symm i =
    if h : i.val < m then Sum.inl ⟨i, h⟩ else Sum.inr ⟨i - m, by omega⟩ := by
  split_ifs with h
  · rw [Equiv.symm_apply_eq]; ext; simp
  · rw [Equiv.symm_apply_eq]; ext; simp; omega

/- English proof (translation)
Simplify using `only [U.blk2, Matrix.reindex_apply, Matrix.submatrix_apply]`. Rewrite using `[fsym, fsym]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem block_two_apply {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D' : Matrix (Fin s) (Fin s) ℂ) (a b : Fin (p + s)) :
    U.blk2 A B' C D' a b =
      if ha : a.val < p then (if hb : b.val < p then A ⟨a, ha⟩ ⟨b, hb⟩ else B' ⟨a, ha⟩ ⟨b - p, by omega⟩)
      else (if hb : b.val < p then C ⟨a - p, by omega⟩ ⟨b, hb⟩ else D' ⟨a - p, by omega⟩ ⟨b - p, by omega⟩) := by
  simp only [U.blk2, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [fsym, fsym]
  split_ifs <;> rfl

/- English proof (translation)
Simplify using `[G.wMat, Matrix.mul_apply]`.
-/
theorem w_mul_apply {d : ℕ} {ι : Type*} (M : Matrix (Fin d) ι ℂ) (a : Fin d) (b : ι) :
    (G.wMat d * M) a b = M a.rev b := by
  simp [G.wMat, Matrix.mul_apply]

/- English proof (translation)
Simplify using `only [G.wMat, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_eq_single b.rev]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Rewrite using `[if_neg]`.

Introduce `h`. Apply `hc` to reduce the goal to its premises. Rewrite using `[h, Fin.rev_rev]`. Simplify using the standard rewrite rules.
-/
theorem mul_w_apply {d : ℕ} {ι : Type*} [Fintype ι] (M : Matrix ι (Fin d) ℂ) (a : ι) (b : Fin d) :
    (M * G.wMat d) a b = M a b.rev := by
  simp only [G.wMat, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single b.rev]
  · simp
  · intro c _ hc; rw [if_neg]; intro h; apply hc; rw [h, Fin.rev_rev]
  · simp

/- English proof (translation)
Rewrite using `[Fin.ext ha, Fin.ext hb]`.
-/
theorem xcongr {j : ℕ} (x : MJ j) {a a' b b' : Fin j} (ha : a.val = a'.val) (hb : b.val = b'.val) :
    x a b = x a' b' := by
  rw [Fin.ext ha, Fin.ext hb]

/- English proof (translation)
Use extensionality with `p q`. Take `⟨X, hX⟩` from `(U.eB k (j + 1) (r - (j + 1))).surjective (Fin.cast (by omega) p)`. Take `⟨Y, hY⟩` from `(U.eB k (j + 1) (r - (j + 1))).surjective (Fin.cast (by omega) q)`. Establish `hp : p.val = (U.eB k (j + 1) (r - (j + 1)) X).val` using `by rw [hX]; rfl`. Establish `hq : q.val = (U.eB k (j + 1) (r - (j + 1)) Y).val` using `by rw [hY]; rfl`.

Establish `e : ∀ M : B.Mat k (j + 1 + (r - (j + 1))), D.castM (by omega : j + 1 + (r - (j + 1)) = r) M p q = M (U.eB k (j + 1) (r - (j + 1)) X) (U.eB k (j + 1) (r - (j + 1)) Y)`. Introduce `M`. Rewrite using `[hX, hY]`. Both sides reduce to the same expression. Rewrite using `[e, Ux4.block3_apply]`.

Apply the tactic sequence `rcases X with ((a | v) | a) <;> rcases Y with ((b | w) | b) <;>`. Apply the tactic sequence `simp only [Ux4.block_index_first_val_eq, Ux4.block_index_middle_val_eq, Ux4.block_index_last_val_eq] at hp hq <;>`. Apply the tactic sequence `simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.zero_apply, levi, Matrix.of_apply, block_two_a …`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega) | skip`. Apply the tactic sequence `all_goals first`.

Consider the case `exact xcongr x (by simp; omega) (by simp; omega)`. Consider the case `(simp only [Complex.star_def]; congr 2; exact xcongr x (by simp; omega) (by simp; omega))`.
-/
theorem levi_eq {k r j : ℕ} (hj : j + 1 ≤ r) (x : MJ j) :
    levi k r j x = D.castM (by omega : j + 1 + (r - (j + 1)) = r)
      (U.blk3 (k := k) (j := j + 1) (ρ := r - (j + 1)) (U.blk2 x 0 0 0) 0 0 0 0 0 0 0
        (G.wMat (j + 1) * U.blk2 (-xᴴ) 0 0 0 * G.wMat (j + 1))) := by
  ext p q
  obtain ⟨X, hX⟩ := (U.eB k (j + 1) (r - (j + 1))).surjective (Fin.cast (by omega) p)
  obtain ⟨Y, hY⟩ := (U.eB k (j + 1) (r - (j + 1))).surjective (Fin.cast (by omega) q)
  have hp : p.val = (U.eB k (j + 1) (r - (j + 1)) X).val := by rw [hX]; rfl
  have hq : q.val = (U.eB k (j + 1) (r - (j + 1)) Y).val := by rw [hY]; rfl
  have e : ∀ M : B.Mat k (j + 1 + (r - (j + 1))),
      D.castM (by omega : j + 1 + (r - (j + 1)) = r) M p q =
        M (U.eB k (j + 1) (r - (j + 1)) X) (U.eB k (j + 1) (r - (j + 1)) Y) := by
    intro M
    rw [hX, hY]; rfl
  rw [e, Ux4.block3_apply]
  rcases X with ((a | v) | a) <;> rcases Y with ((b | w) | b) <;>
    simp only [Ux4.block_index_first_val_eq, Ux4.block_index_middle_val_eq, Ux4.block_index_last_val_eq] at hp hq <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, levi, Matrix.of_apply, block_two_apply, w_mul_apply, mul_w_apply,
      Matrix.mul_assoc, Fin.val_rev, Matrix.neg_apply, Matrix.conjTranspose_apply] <;>
    split_ifs <;> first | rfl | (exfalso; omega) | skip
  all_goals first
    | exact xcongr x (by simp; omega) (by simp; omega)
    | (simp only [Complex.star_def]; congr 2; exact xcongr x (by simp; omega) (by simp; omega))

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential
