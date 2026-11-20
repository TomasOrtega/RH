import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.NormalRow

variable {K : Type} [Field K] {n ρ p : ℕ}

/- English proof (translation)
Unfold `cT`. Rewrite using `[Matrix.map_mul, Matrix.transpose_mul]`.
-/
theorem cTm (σ : K →+* K) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) K) (y : Matrix (Fin b) (Fin c) K) :
    cT σ (x * y) = cT σ y * cT σ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT]`.
-/
theorem cTa (σ : K →+* K) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) K) : cT σ (x + y) = cT σ x + cT σ y := by
  ext i j
  simp [cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT]`.
-/
theorem cTn (σ : K →+* K) {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) : cT σ (-x) = -cT σ x := by
  ext i j
  simp [cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT]`.
-/
theorem cTs (σ : K →+* K) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) K) : cT σ (x - y) = cT σ x - cT σ y := by
  ext i j
  simp [cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT]`.
-/
theorem cTz (σ : K →+* K) {a b : ℕ} : cT σ (0 : Matrix (Fin a) (Fin b) K) = 0 := by
  ext i j
  simp [cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, hσ]`.
-/
theorem cTc (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) :
    cT σ (cT σ x) = x := by
  ext i j
  simp [cT, hσ]

/- English proof (translation)
Unfold `bl`. Rewrite using `[Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`.
-/
theorem mulB {R : Type} [CommRing R] (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) R)
    (b b' : Matrix (Fin ρ) (Fin p) R) (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

/- English proof (translation)
Unfold `bl`. Rewrite using `[← Matrix.fromBlocks_add]`. Both sides reduce to the same expression.
-/
theorem addB {R : Type} [CommRing R] (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) R)
    (b b' : Matrix (Fin ρ) (Fin p) R) (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  unfold bl
  rw [← Matrix.fromBlocks_add]
  rfl

/- English proof (translation)
Unfold `bl`. Rewrite using `[Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]`.
-/
theorem oneB {R : Type} [CommRing R] (hn : ρ + p = n) :
    bl hn (1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (1 : Matrix (Fin p) (Fin p) R) = 1 := by
  unfold bl
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

/- English proof (translation)
Establish `h' : Matrix.fromBlocks a b c d = Matrix.fromBlocks a' b' c' d'`. Use extensionality with `i j`. Use `congrFun (congrFun h ((finSumFinEquiv.trans (finCongr hn)) i)) ((finSumFinEquiv.trans (finCongr hn)) j)` as an intermediate fact. Simplify using `only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply] at this`. Conclude with `this`.

Conclude with `Matrix.fromBlocks_inj.1 h'`.
-/
theorem injB {R : Type} (hn : ρ + p = n) {a a' : Matrix (Fin ρ) (Fin ρ) R}
    {b b' : Matrix (Fin ρ) (Fin p) R} {c c' : Matrix (Fin p) (Fin ρ) R} {d d' : Matrix (Fin p) (Fin p) R}
    (h : bl hn a b c d = bl hn a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h' : Matrix.fromBlocks a b c d = Matrix.fromBlocks a' b' c' d' := by
    ext i j
    have := congrFun (congrFun h ((finSumFinEquiv.trans (finCongr hn)) i)) ((finSumFinEquiv.trans (finCongr hn)) j)
    simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply] at this
    exact this
  exact Matrix.fromBlocks_inj.1 h'

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [cT, bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]`. Apply the tactic sequence `rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>`. Apply the tactic sequence `rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl`.
-/
theorem cTB (σ : K →+* K) (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) K) (b : Matrix (Fin ρ) (Fin p) K)
    (c : Matrix (Fin p) (Fin ρ) K) (d : Matrix (Fin p) (Fin p) K) :
    cT σ (bl hn a b c d) = bl hn (cT σ a) (cT σ c) (cT σ b) (cT σ d) := by
  ext i j
  simp only [cT, bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

/- English proof (translation)
Establish `hJJ : (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) K) * blk4 0 (-1) 1 0 = 1`. Rewrite using `[submatrix_fromBlocks_mul]`. Simplify using `[BigCell.block_identity_eq_one]`. Establish `hJJ' : (blk4 0 (-1) 1 0 : Matrix (Fin (n + n)) (Fin (n + n)) K) * blk4 0 1 (-1) 0 = 1`. Rewrite using `[submatrix_fromBlocks_mul]`.

Simplify using `[BigCell.block_identity_eq_one]`. Establish `h0 : cT σ (blk4 A B C E) * blk4 0 1 (-1) 0 * blk4 A B C E = blk4 0 1 (-1) 0` using `h`. Establish `h1 : (blk4 0 (-1) 1 0 * cT σ (blk4 A B C E) * blk4 0 1 (-1) 0) * blk4 A B C E = 1`. Rewrite using `[mul_assoc (blk4 0 (-1) 1 0), mul_assoc (blk4 0 (-1) 1 0), h0, hJJ']`. Establish `h2` using `mul_eq_one_comm.1 h1`.

Establish `h3 : blk4 A B C E * blk4 0 (-1) 1 0 * cT σ (blk4 A B C E) = blk4 0 (-1) 1 0`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc, hJJ, mul_one]`. Use `_ = _ := by rw [h2, one_mul]`. Rewrite `h3` using `[BigCell.cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]`.

Take `⟨e1, e2, -, e4⟩` from `blockMatrixTwoByTwoFin_injective h3`. Simplify using `only [mul_zero, mul_neg, mul_one, zero_add, add_zero, neg_mul] at e1 e2 e4`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: B * cT σ A - A * cT σ B = 0` using `by simpa [sub_eq_add_neg, add_comm] using e1`. Conclude with `(sub_eq_zero.1 this).symm`.

Establish `: B * cT σ C - A * cT σ E = -1` using `by simpa [sub_eq_add_neg, add_comm] using e2`. Rewrite using `[← sub_eq_zero]`. Rewrite using `[← neg_eq_zero]`. Establish `e : -(A * cT σ E - (1 + B * cT σ C)) = B * cT σ C - A * cT σ E + 1` using `by abel`. Rewrite using `[e, this]`.

Simplify using the standard rewrite rules. Establish `: E * cT σ C - C * cT σ E = 0` using `by simpa [sub_eq_add_neg, add_comm] using e4`. Conclude with `(sub_eq_zero.1 this).symm`.
-/
theorem what₂ (σ : K →+* K) {A B C E : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (blk4 0 1 (-1) 0) (blk4 A B C E)) :
    A * cT σ B = B * cT σ A ∧ A * cT σ E = 1 + B * cT σ C ∧ C * cT σ E = E * cT σ C := by
  have hJJ : (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) K) * blk4 0 (-1) 1 0 = 1 := by
    rw [submatrix_fromBlocks_mul]
    simp [BigCell.block_identity_eq_one]
  have hJJ' : (blk4 0 (-1) 1 0 : Matrix (Fin (n + n)) (Fin (n + n)) K) * blk4 0 1 (-1) 0 = 1 := by
    rw [submatrix_fromBlocks_mul]
    simp [BigCell.block_identity_eq_one]
  have h0 : cT σ (blk4 A B C E) * blk4 0 1 (-1) 0 * blk4 A B C E = blk4 0 1 (-1) 0 := h
  have h1 : (blk4 0 (-1) 1 0 * cT σ (blk4 A B C E) * blk4 0 1 (-1) 0) * blk4 A B C E = 1 := by
    rw [mul_assoc (blk4 0 (-1) 1 0), mul_assoc (blk4 0 (-1) 1 0), h0, hJJ']
  have h2 := mul_eq_one_comm.1 h1
  have h3 : blk4 A B C E * blk4 0 (-1) 1 0 * cT σ (blk4 A B C E) = blk4 0 (-1) 1 0 := by
    calc _ = blk4 A B C E * (blk4 0 (-1) 1 0 * cT σ (blk4 A B C E) * blk4 0 1 (-1) 0) * blk4 0 (-1) 1 0 := by
          simp only [mul_assoc, hJJ, mul_one]
      _ = _ := by rw [h2, one_mul]
  rw [BigCell.cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h3
  obtain ⟨e1, e2, -, e4⟩ := blockMatrixTwoByTwoFin_injective h3
  simp only [mul_zero, mul_neg, mul_one, zero_add, add_zero, neg_mul] at e1 e2 e4
  refine ⟨?_, ?_, ?_⟩
  · have : B * cT σ A - A * cT σ B = 0 := by simpa [sub_eq_add_neg, add_comm] using e1
    exact (sub_eq_zero.1 this).symm
  · have : B * cT σ C - A * cT σ E = -1 := by simpa [sub_eq_add_neg, add_comm] using e2
    rw [← sub_eq_zero]
    rw [← neg_eq_zero]
    have e : -(A * cT σ E - (1 + B * cT σ C)) = B * cT σ C - A * cT σ E + 1 := by abel
    rw [e, this]
    simp
  · have : E * cT σ C - C * cT σ E = 0 := by simpa [sub_eq_add_neg, add_comm] using e4
    exact (sub_eq_zero.1 this).symm

/- English proof (translation)
Establish `e : (a₄ + a₃ * X) * cT σ d - (b₄ + a₃ * Y) * cT σ c - 1 = (a₃ * cT σ W + a₄ * cT σ d - (1 + b₄ * cT σ c)) + a₃ * (-cT σ W + X * cT σ d - Y * cT σ c)`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite `e` using `[sub_eq_zero.2 h5, sub_eq_zero.2 h2, Matrix.mul_zero, add_zero]`. Conclude with `sub_eq_zero.1 e`.
-/
theorem rel_ad (σ : K →+* K) {a₃ W : Matrix (Fin p) (Fin ρ) K} {a₄ b₄ c d : Matrix (Fin p) (Fin p) K}
    {X Y : Matrix (Fin ρ) (Fin p) K}
    (h2 : -cT σ W + X * cT σ d = Y * cT σ c)
    (h5 : a₃ * cT σ W + a₄ * cT σ d = 1 + b₄ * cT σ c) :
    (a₄ + a₃ * X) * cT σ d - (b₄ + a₃ * Y) * cT σ c = 1 := by
  have e : (a₄ + a₃ * X) * cT σ d - (b₄ + a₃ * Y) * cT σ c - 1 =
      (a₃ * cT σ W + a₄ * cT σ d - (1 + b₄ * cT σ c)) + a₃ * (-cT σ W + X * cT σ d - Y * cT σ c) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_assoc]
    abel
  rw [sub_eq_zero.2 h5, sub_eq_zero.2 h2, Matrix.mul_zero, add_zero] at e
  exact sub_eq_zero.1 e

/- English proof (translation)
Establish `h6' : Z * cT σ a₃ + Y * cT σ a₄ = -cT σ b₃ + X * cT σ b₄`. Use `congrArg (cT σ) h6` as an intermediate fact. Simplify `this` using `only [cTa, cTm, cTn, cTc σ hσ]`. Establish `e : (a₄ + a₃ * X) * cT σ (b₄ + a₃ * Y) - (b₄ + a₃ * Y) * cT σ (a₄ + a₃ * X) = ((a₃ * cT σ b₃ + a₄ * cT σ b₄) - (b₃ * cT σ a₃ + b₄ * cT σ a₄)) + ((a₃ * cT σ Z + a₄ * cT σ Y) - (-b₃ + b₄ * cT σ X)) * cT σ a₃ + a₃ * (((-cT σ Z + X * cT σ Y) - (-Z + Y * cT σ X)) * cT σ a₃) - a₃ * ((Z …`. Simplify using `only [cTa, cTm, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]`.

Normalize the expressions using the abelian group laws. Rewrite `e` using `[sub_eq_zero.2 h7, sub_eq_zero.2 h6, sub_eq_zero.2 h1, sub_eq_zero.2 h6']`. Simplify using `only [Matrix.zero_mul, Matrix.mul_zero, add_zero, sub_zero] at e`. Conclude with `sub_eq_zero.1 e`.
-/
theorem rel_ab (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {a₃ b₃ : Matrix (Fin p) (Fin ρ) K}
    {a₄ b₄ : Matrix (Fin p) (Fin p) K} {X Y : Matrix (Fin ρ) (Fin p) K} {Z : Matrix (Fin ρ) (Fin ρ) K}
    (h1 : -cT σ Z + X * cT σ Y = -Z + Y * cT σ X)
    (h6 : a₃ * cT σ Z + a₄ * cT σ Y = -b₃ + b₄ * cT σ X)
    (h7 : a₃ * cT σ b₃ + a₄ * cT σ b₄ = b₃ * cT σ a₃ + b₄ * cT σ a₄) :
    (a₄ + a₃ * X) * cT σ (b₄ + a₃ * Y) = (b₄ + a₃ * Y) * cT σ (a₄ + a₃ * X) := by
  have h6' : Z * cT σ a₃ + Y * cT σ a₄ = -cT σ b₃ + X * cT σ b₄ := by
    have := congrArg (cT σ) h6
    simpa only [cTa, cTm, cTn, cTc σ hσ] using this
  have e : (a₄ + a₃ * X) * cT σ (b₄ + a₃ * Y) - (b₄ + a₃ * Y) * cT σ (a₄ + a₃ * X) =
      ((a₃ * cT σ b₃ + a₄ * cT σ b₄) - (b₃ * cT σ a₃ + b₄ * cT σ a₄))
      + ((a₃ * cT σ Z + a₄ * cT σ Y) - (-b₃ + b₄ * cT σ X)) * cT σ a₃
      + a₃ * (((-cT σ Z + X * cT σ Y) - (-Z + Y * cT σ X)) * cT σ a₃)
      - a₃ * ((Z * cT σ a₃ + Y * cT σ a₄) - (-cT σ b₃ + X * cT σ b₄)) := by
    simp only [cTa, cTm, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_assoc]
    abel
  rw [sub_eq_zero.2 h7, sub_eq_zero.2 h6, sub_eq_zero.2 h1, sub_eq_zero.2 h6'] at e
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, sub_zero] at e
  exact sub_eq_zero.1 e

/- English proof (translation)
Establish `r1' : d * cT σ a - c * cT σ b = 1`. Use `congrArg (cT σ) r1` as an intermediate fact. Simplify `this` using `only [cTs, cTm, cTc σ hσ, BigCell.cT_one_sq]`. Establish `hm : blk4 a b c d * blk4 (cT σ d) (-cT σ b) (-cT σ c) (cT σ a) = 1`. Rewrite using `[submatrix_fromBlocks_mul]`.

Establish `e1 : a * cT σ d + b * -cT σ c = 1` using `by rw [mul_neg, ← sub_eq_add_neg]; exact r1`. Establish `e2 : a * -cT σ b + b * cT σ a = 0` using `by rw [mul_neg, r2]; simp`. Establish `e3 : c * cT σ d + d * -cT σ c = 0` using `by rw [mul_neg, r3]; simp`. Establish `e4 : c * -cT σ b + d * cT σ a = 1` using `by rw [mul_neg, ← r1']; abel`. Rewrite using `[e1, e2, e3, e4, BigCell.block_identity_eq_one]`.

Conclude with `mul_eq_one_comm.1 hm`.
-/
theorem y_inv (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {a b c d : Matrix (Fin p) (Fin p) K}
    (r1 : a * cT σ d - b * cT σ c = 1) (r2 : a * cT σ b = b * cT σ a) (r3 : c * cT σ d = d * cT σ c) :
    blk4 (cT σ d) (-cT σ b) (-cT σ c) (cT σ a) * blk4 a b c d = 1 := by
  have r1' : d * cT σ a - c * cT σ b = 1 := by
    have := congrArg (cT σ) r1
    simpa only [cTs, cTm, cTc σ hσ, BigCell.cT_one_sq] using this
  have hm : blk4 a b c d * blk4 (cT σ d) (-cT σ b) (-cT σ c) (cT σ a) = 1 := by
    rw [submatrix_fromBlocks_mul]
    have e1 : a * cT σ d + b * -cT σ c = 1 := by rw [mul_neg, ← sub_eq_add_neg]; exact r1
    have e2 : a * -cT σ b + b * cT σ a = 0 := by rw [mul_neg, r2]; simp
    have e3 : c * cT σ d + d * -cT σ c = 0 := by rw [mul_neg, r3]; simp
    have e4 : c * -cT σ b + d * cT σ a = 1 := by rw [mul_neg, ← r1']; abel
    rw [e1, e2, e3, e4, BigCell.block_identity_eq_one]
  exact mul_eq_one_comm.1 hm

/- English proof (translation)
Establish `hv` using `y_inv σ hσ r1 r2 r3`. Rewrite `hv` using `[submatrix_fromBlocks_mul, ← BigCell.block_identity_eq_one]`. Conclude with `blockMatrixTwoByTwoFin_injective hv`.
-/
theorem y_left (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {a b c d : Matrix (Fin p) (Fin p) K}
    (r1 : a * cT σ d - b * cT σ c = 1) (r2 : a * cT σ b = b * cT σ a) (r3 : c * cT σ d = d * cT σ c) :
    cT σ d * a + -cT σ b * c = 1 ∧ cT σ d * b + -cT σ b * d = 0 ∧
      -cT σ c * a + cT σ a * c = 0 ∧ -cT σ c * b + cT σ a * d = 1 := by
  have hv := y_inv σ hσ r1 r2 r3
  rw [submatrix_fromBlocks_mul, ← BigCell.block_identity_eq_one] at hv
  exact blockMatrixTwoByTwoFin_injective hv

/- English proof (translation)
Take `⟨l1, l2, l3, l4⟩` from `y_left σ hσ r1 r2 r3`. Establish `f3 : -cT σ d * a + cT σ b * c = -1`. Rewrite using `[← l1, neg_mul, neg_mul]`. Normalize the expressions using the abelian group laws. Establish `f4 : -cT σ d * b + cT σ b * d = 0`.

Rewrite using `[neg_mul]`. Rewrite `l2` using `[neg_mul]`. Rewrite using `[← neg_eq_zero, ← l2]`. Normalize the expressions using the abelian group laws. Unfold `IsUnitary`.

Rewrite using `[BigCell.cT_blk4, submatrix_fromBlocks_mul]`. Simplify using `only [mul_zero, mul_neg, mul_one, zero_add, add_zero]`. Rewrite using `[submatrix_fromBlocks_mul, l3, l4, f3, f4]`.
-/
theorem y_unit (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {a b c d : Matrix (Fin p) (Fin p) K}
    (r1 : a * cT σ d - b * cT σ c = 1) (r2 : a * cT σ b = b * cT σ a) (r3 : c * cT σ d = d * cT σ c) :
    IsUnitary σ (blk4 0 1 (-1) 0) (blk4 a b c d) := by
  obtain ⟨l1, l2, l3, l4⟩ := y_left σ hσ r1 r2 r3
  have f3 : -cT σ d * a + cT σ b * c = -1 := by
    rw [← l1, neg_mul, neg_mul]
    abel
  have f4 : -cT σ d * b + cT σ b * d = 0 := by
    rw [neg_mul]
    rw [neg_mul] at l2
    rw [← neg_eq_zero, ← l2]
    abel
  unfold IsUnitary
  rw [BigCell.cT_blk4, submatrix_fromBlocks_mul]
  simp only [mul_zero, mul_neg, mul_one, zero_add, add_zero]
  rw [submatrix_fromBlocks_mul, l3, l4, f3, f4]

/- English proof (translation)
Substitute `hT` using the available equality. Prove the components needed by the constructor for the conclusion. Establish `e : cT σ W * a + (-(X * cT σ b) + Y * cT σ a) * c - X = X * (cT σ d * a + -cT σ b * c - 1) - (-cT σ W + X * cT σ d - Y * cT σ c) * a + Y * (-cT σ c * a + cT σ a * c)`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_one]`. Normalize the expressions using the abelian group laws.

Rewrite `e` using `[sub_eq_zero.2 l1, sub_eq_zero.2 h2, l3]`. Simplify using `only [Matrix.zero_mul, Matrix.mul_zero, add_zero, sub_zero] at e`. Conclude with `(sub_eq_zero.1 e).symm`. Establish `e : cT σ W * b + (-(X * cT σ b) + Y * cT σ a) * d - Y = Y * (-cT σ c * b + cT σ a * d - 1) - (-cT σ W + X * cT σ d - Y * cT σ c) * b + X * (cT σ d * b + -cT σ b * d)`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_one]`.

Normalize the expressions using the abelian group laws. Rewrite `e` using `[sub_eq_zero.2 l4, sub_eq_zero.2 h2, l2]`. Simplify using `only [Matrix.zero_mul, Matrix.mul_zero, add_zero, sub_zero] at e`. Conclude with `(sub_eq_zero.1 e).symm`.
-/
theorem xy_eq (σ : K →+* K) {X Y T : Matrix (Fin ρ) (Fin p) K} {W : Matrix (Fin p) (Fin ρ) K}
    {a b c d : Matrix (Fin p) (Fin p) K} (hT : T = -(X * cT σ b) + Y * cT σ a)
    (h2 : -cT σ W + X * cT σ d = Y * cT σ c)
    (l1 : cT σ d * a + -cT σ b * c = 1) (l2 : cT σ d * b + -cT σ b * d = 0)
    (l3 : -cT σ c * a + cT σ a * c = 0) (l4 : -cT σ c * b + cT σ a * d = 1) :
    X = cT σ W * a + T * c ∧ Y = cT σ W * b + T * d := by
  subst hT
  constructor
  · have e : cT σ W * a + (-(X * cT σ b) + Y * cT σ a) * c - X =
        X * (cT σ d * a + -cT σ b * c - 1) - (-cT σ W + X * cT σ d - Y * cT σ c) * a
          + Y * (-cT σ c * a + cT σ a * c) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg,
        Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_one]
      abel
    rw [sub_eq_zero.2 l1, sub_eq_zero.2 h2, l3] at e
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, sub_zero] at e
    exact (sub_eq_zero.1 e).symm
  · have e : cT σ W * b + (-(X * cT σ b) + Y * cT σ a) * d - Y =
        Y * (-cT σ c * b + cT σ a * d - 1) - (-cT σ W + X * cT σ d - Y * cT σ c) * b
          + X * (cT σ d * b + -cT σ b * d) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg,
        Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_one]
      abel
    rw [sub_eq_zero.2 l4, sub_eq_zero.2 h2, l2] at e
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, sub_zero] at e
    exact (sub_eq_zero.1 e).symm

/- English proof (translation)
Establish `r1' : d * cT σ a - c * cT σ b = 1`. Use `congrArg (cT σ) r1` as an intermediate fact. Simplify `this` using `only [cTs, cTm, cTc σ hσ, BigCell.cT_one_sq]`. Establish `key : X * cT σ Y - Y * cT σ X = cT σ W * cT σ T - T * W`. Establish `e : X * cT σ Y - Y * cT σ X - (cT σ W * cT σ T - T * W) = cT σ W * ((a * cT σ b - b * cT σ a) * W) + cT σ W * ((a * cT σ d - b * cT σ c - 1) * cT σ T) - T * ((d * cT σ a - c * cT σ b - 1) * W) + T * ((c * cT σ d - d * cT σ c) * cT σ T)`.

Rewrite using `[hX, hY]`. Simplify using `only [cTa, cTm, cTc σ hσ, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Rewrite `e` using `[sub_eq_zero.2 r2, sub_eq_zero.2 r1, sub_eq_zero.2 r1', sub_eq_zero.2 r3]`. Simplify using `only [Matrix.zero_mul, Matrix.mul_zero, add_zero, sub_zero] at e`.

Conclude with `sub_eq_zero.1 e`. Establish `e : cT σ (-Z + T * W) - (-Z + T * W) = ((-cT σ Z + X * cT σ Y) - (-Z + Y * cT σ X)) - ((X * cT σ Y - Y * cT σ X) - (cT σ W * cT σ T - T * W))`. Simplify using `only [cTa, cTn, cTm, cTc σ hσ]`. Normalize the expressions using the abelian group laws. Rewrite `e` using `[sub_eq_zero.2 h1, sub_eq_zero.2 key, sub_zero]`.

Conclude with `sub_eq_zero.1 e`.
-/
theorem herm_zeta (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {Z : Matrix (Fin ρ) (Fin ρ) K}
    {X Y T : Matrix (Fin ρ) (Fin p) K} {W : Matrix (Fin p) (Fin ρ) K}
    {a b c d : Matrix (Fin p) (Fin p) K}
    (hX : X = cT σ W * a + T * c) (hY : Y = cT σ W * b + T * d)
    (h1 : -cT σ Z + X * cT σ Y = -Z + Y * cT σ X)
    (r1 : a * cT σ d - b * cT σ c = 1) (r2 : a * cT σ b = b * cT σ a) (r3 : c * cT σ d = d * cT σ c) :
    cT σ (-Z + T * W) = -Z + T * W := by
  have r1' : d * cT σ a - c * cT σ b = 1 := by
    have := congrArg (cT σ) r1
    simpa only [cTs, cTm, cTc σ hσ, BigCell.cT_one_sq] using this
  have key : X * cT σ Y - Y * cT σ X = cT σ W * cT σ T - T * W := by
    have e : X * cT σ Y - Y * cT σ X - (cT σ W * cT σ T - T * W) =
        cT σ W * ((a * cT σ b - b * cT σ a) * W) + cT σ W * ((a * cT σ d - b * cT σ c - 1) * cT σ T)
          - T * ((d * cT σ a - c * cT σ b - 1) * W) + T * ((c * cT σ d - d * cT σ c) * cT σ T) := by
      rw [hX, hY]
      simp only [cTa, cTm, cTc σ hσ, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
      abel
    rw [sub_eq_zero.2 r2, sub_eq_zero.2 r1, sub_eq_zero.2 r1', sub_eq_zero.2 r3] at e
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, sub_zero] at e
    exact sub_eq_zero.1 e
  have e : cT σ (-Z + T * W) - (-Z + T * W) =
      ((-cT σ Z + X * cT σ Y) - (-Z + Y * cT σ X)) - ((X * cT σ Y - Y * cT σ X) - (cT σ W * cT σ T - T * W)) := by
    simp only [cTa, cTn, cTm, cTc σ hσ]
    abel
  rw [sub_eq_zero.2 h1, sub_eq_zero.2 key, sub_zero] at e
  exact sub_eq_zero.1 e

/- English proof (translation)
Introduce `K _ σ hσ n ρ p hn a₁ b₁ Z a₂ b₂ X Y a₃ b₃ W a₄ b₄ c' d' hu _`. Take `⟨f1, f2, f3⟩` from `what₂ σ hu`. Establish `hm1 : cT σ (-1 : Matrix (Fin ρ) (Fin ρ) K) = -1` using `by rw [cTn, BigCell.cT_one_sq]`. Rewrite `f1` using `[cTB, cTB, mulB, mulB]`. Rewrite `f2` using `[cTB, cTB, mulB, mulB, ← oneB hn, addB]`.

Rewrite `f3` using `[cTB, cTB, mulB, mulB]`. Take `⟨-, -, -, h7⟩` from `injB hn f1`. Take `⟨-, -, h6, h5⟩` from `injB hn f2`. Take `⟨h1, h2, -, h4⟩` from `injB hn f3`. Simplify using `only [hm1, cTz, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add] at h1 h2 h4 h5 h6 h7`.

Establish `r1` using `rel_ad σ h2 h5`. Establish `r2` using `rel_ab σ hσ h1 h6 h7`. Generalize the expression as in `a₄ + a₃ * X = a' at r1 r2 ⊢`. Generalize the expression as in `b₄ + a₃ * Y = b' at r1 r2 ⊢`. Take `⟨l1, l2, l3, l4⟩` from `y_left σ hσ r1 r2 h4`.

Take `⟨T, hT⟩ : ∃ T, T = -(X * cT σ b') + Y * cT σ a'` from `⟨_, rfl⟩`. Take `⟨hX, hY⟩` from `xy_eq σ hT h2 l1 l2 l3 l4`. Establish `hη : -cT σ (-cT σ W) = W` using `by rw [cTn, cTc σ hσ, neg_neg]`. Use `⟨-Z + T * W, -cT σ W, bl hn 1 T 0 1, Matrix.isUnit_det_of_left_inverse (y_inv σ hσ r1 r2 h4), y_unit σ hσ r1 r2 h4, herm_zeta σ hσ hX hY h1 r1 r2 h4, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[rowC, mulB]`.

Simplify using `only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, Matrix.neg_mul, neg_neg, add_zero, zero_add]`. Rewrite using `[← hX]`. Rewrite using `[rowD, mulB, hη]`. Simplify using `only [Matrix.one_mul, Matrix.zero_mul, Matrix.neg_mul, neg_neg, add_zero, zero_add]`. Establish `e1 : -(-Z + T * W) + T * W = Z` using `by abel`.

Rewrite using `[e1, ← hY]`.
-/
theorem normal_form : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a₁ b₁ Z : Matrix (Fin ρ) (Fin ρ) K) (a₂ b₂ X Y : Matrix (Fin ρ) (Fin p) K)
      (a₃ b₃ W : Matrix (Fin p) (Fin ρ) K) (a₄ b₄ c' d' : Matrix (Fin p) (Fin p) K),
    IsUnitary σ (blk4 0 1 (-1) 0) (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')) →
    IsUnit (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')).det →
    ∃ (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
      IsUnit (blk4 (a₄ + a₃ * X) (b₄ + a₃ * Y) c' d').det ∧ IsUnitary σ (blk4 0 1 (-1) 0) (blk4 (a₄ + a₃ * X) (b₄ + a₃ * Y) c' d') ∧
      cT σ ζ = ζ ∧ bl hn (-1) X 0 c' = T * rowC hn η (a₄ + a₃ * X) c' ∧ bl hn Z Y W d' = T * rowD hn σ ζ η (b₄ + a₃ * Y) d' := by
  intro K _ σ hσ n ρ p hn a₁ b₁ Z a₂ b₂ X Y a₃ b₃ W a₄ b₄ c' d' hu _
  obtain ⟨f1, f2, f3⟩ := what₂ σ hu
  have hm1 : cT σ (-1 : Matrix (Fin ρ) (Fin ρ) K) = -1 := by rw [cTn, BigCell.cT_one_sq]
  rw [cTB, cTB, mulB, mulB] at f1
  rw [cTB, cTB, mulB, mulB, ← oneB hn, addB] at f2
  rw [cTB, cTB, mulB, mulB] at f3
  obtain ⟨-, -, -, h7⟩ := injB hn f1
  obtain ⟨-, -, h6, h5⟩ := injB hn f2
  obtain ⟨h1, h2, -, h4⟩ := injB hn f3
  simp only [hm1, cTz, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_one,
    add_zero, zero_add] at h1 h2 h4 h5 h6 h7
  have r1 := rel_ad σ h2 h5
  have r2 := rel_ab σ hσ h1 h6 h7
  generalize a₄ + a₃ * X = a' at r1 r2 ⊢
  generalize b₄ + a₃ * Y = b' at r1 r2 ⊢
  obtain ⟨l1, l2, l3, l4⟩ := y_left σ hσ r1 r2 h4
  obtain ⟨T, hT⟩ : ∃ T, T = -(X * cT σ b') + Y * cT σ a' := ⟨_, rfl⟩
  obtain ⟨hX, hY⟩ := xy_eq σ hT h2 l1 l2 l3 l4
  have hη : -cT σ (-cT σ W) = W := by rw [cTn, cTc σ hσ, neg_neg]
  refine ⟨-Z + T * W, -cT σ W, bl hn 1 T 0 1, Matrix.isUnit_det_of_left_inverse (y_inv σ hσ r1 r2 h4),
    y_unit σ hσ r1 r2 h4, herm_zeta σ hσ hX hY h1 r1 r2 h4, ?_, ?_⟩
  · rw [rowC, mulB]
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, Matrix.neg_mul, neg_neg, add_zero, zero_add]
    rw [← hX]
  · rw [rowD, mulB, hη]
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.neg_mul, neg_neg, add_zero, zero_add]
    have e1 : -(-Z + T * W) + T * W = Z := by abel
    rw [e1, ← hY]

end GlobalTheory.CompanionTheory.ZUnf.NormalRow
