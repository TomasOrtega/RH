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

namespace GlobalTheory.CompanionTheory.ZUnf.ClassRep

variable {K : Type} [Field K]

/- English proof (translation)
Simplify using `only [blk4]`. Rewrite using `[Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`.
-/
theorem blkMul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

/- English proof (translation)
Establish `h'` using `congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h`. Simplify using `only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h'`. Conclude with `Matrix.fromBlocks_inj.mp h'`.
-/
theorem blkInj {n : ℕ} {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h' := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h'
  exact Matrix.fromBlocks_inj.mp h'

/- English proof (translation)
Simplify using `only [bl]`. Rewrite using `[Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`.
-/
theorem blMul {n ρ p : ℕ} (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) K)
    (b b' : Matrix (Fin ρ) (Fin p) K) (c c' : Matrix (Fin p) (Fin ρ) K) (d d' : Matrix (Fin p) (Fin p) K) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

/- English proof (translation)
Simplify using `only [PositivityTheory.GramSchwartzFunctions.EC.cT, Matrix.map_mul, Matrix.transpose_mul]`.
-/
theorem cTMul (σ : K →+* K) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) K) (y : Matrix (Fin b) (Fin c) K) :
    PositivityTheory.GramSchwartzFunctions.EC.cT σ (x * y) = PositivityTheory.GramSchwartzFunctions.EC.cT σ y * PositivityTheory.GramSchwartzFunctions.EC.cT σ x := by
  simp only [PositivityTheory.GramSchwartzFunctions.EC.cT, Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[PositivityTheory.GramSchwartzFunctions.EC.cT]`.
-/
theorem cTAdd (σ : K →+* K) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) K) :
    PositivityTheory.GramSchwartzFunctions.EC.cT σ (x + y) = PositivityTheory.GramSchwartzFunctions.EC.cT σ x + PositivityTheory.GramSchwartzFunctions.EC.cT σ y := by
  ext i j
  simp [PositivityTheory.GramSchwartzFunctions.EC.cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[PositivityTheory.GramSchwartzFunctions.EC.cT]`.
-/
theorem cTZero (σ : K →+* K) {a b : ℕ} : PositivityTheory.GramSchwartzFunctions.EC.cT σ (0 : Matrix (Fin a) (Fin b) K) = 0 := by
  ext i j
  simp [PositivityTheory.GramSchwartzFunctions.EC.cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[PositivityTheory.GramSchwartzFunctions.EC.cT, hσ]`.
-/
theorem cTInvol (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) :
    PositivityTheory.GramSchwartzFunctions.EC.cT σ (PositivityTheory.GramSchwartzFunctions.EC.cT σ x) = x := by
  ext i j
  simp [PositivityTheory.GramSchwartzFunctions.EC.cT, hσ]

/- English proof (translation)
Simplify using `only [PositivityTheory.GramSchwartzFunctions.EC.cT, blk4]`. Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]`. Apply the tactic sequence `rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp`.
-/
theorem cTBlk (σ : K →+* K) {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    PositivityTheory.GramSchwartzFunctions.EC.cT σ (blk4 a b c d) =
      blk4 (PositivityTheory.GramSchwartzFunctions.EC.cT σ a) (PositivityTheory.GramSchwartzFunctions.EC.cT σ c) (PositivityTheory.GramSchwartzFunctions.EC.cT σ b) (PositivityTheory.GramSchwartzFunctions.EC.cT σ d) := by
  simp only [PositivityTheory.GramSchwartzFunctions.EC.cT, blk4]
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

/- English proof (translation)
Unfold `PositivityTheory.GramSchwartzFunctions.EC.IsUnitary at hU`. Rewrite `hU` using `[cTBlk, blkMul, blkMul]`. Take `⟨-, h12, h21, h22⟩` from `blkInj hU`. Simplify using `only [cTZero, neg_zero, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul, Matrix.mul_neg, Matrix.neg_mul, mul_neg, neg_mul] at h12 h21 h22`. Establish `e2 : PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd * A = 1` using `neg_injective h21`.

Establish `e3 : PositivityTheory.GramSchwartzFunctions.EC.cT σ B * Dd = PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd * B`. Conclude with `(neg_add_eq_zero.mp h22).symm`. Establish `e4 : Dd * PositivityTheory.GramSchwartzFunctions.EC.cT σ A = 1` using `mul_eq_one_comm.mp h12`. Establish `e5 : A * PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd = 1` using `mul_eq_one_comm.mp e2`. Use `⟨e4, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (A * PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd) * B * PositivityTheory.GramSchwartzFunctions.EC.cT σ A := by`. Rewrite using `[e3]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = B * PositivityTheory.GramSchwartzFunctions.EC.cT σ A := by rw [e5, one_mul]`.
-/
theorem siegel_relations (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {p : ℕ}
    {A B Dd : Matrix (Fin p) (Fin p) K}
    (hU : PositivityTheory.GramSchwartzFunctions.EC.IsUnitary σ (blk4 0 1 (-1) 0) (blk4 A B 0 Dd)) :
    Dd * PositivityTheory.GramSchwartzFunctions.EC.cT σ A = 1 ∧
      A * PositivityTheory.GramSchwartzFunctions.EC.cT σ B = B * PositivityTheory.GramSchwartzFunctions.EC.cT σ A := by
  unfold PositivityTheory.GramSchwartzFunctions.EC.IsUnitary at hU
  rw [cTBlk, blkMul, blkMul] at hU
  obtain ⟨-, h12, h21, h22⟩ := blkInj hU
  simp only [cTZero, neg_zero, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul, Matrix.mul_neg,
    Matrix.neg_mul, mul_neg, neg_mul] at h12 h21 h22
  have e2 : PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd * A = 1 := neg_injective h21
  have e3 : PositivityTheory.GramSchwartzFunctions.EC.cT σ B * Dd = PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd * B := by
    exact (neg_add_eq_zero.mp h22).symm
  have e4 : Dd * PositivityTheory.GramSchwartzFunctions.EC.cT σ A = 1 := mul_eq_one_comm.mp h12
  have e5 : A * PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd = 1 := mul_eq_one_comm.mp e2
  refine ⟨e4, ?_⟩
  calc A * PositivityTheory.GramSchwartzFunctions.EC.cT σ B
      = A * PositivityTheory.GramSchwartzFunctions.EC.cT σ B * (Dd * PositivityTheory.GramSchwartzFunctions.EC.cT σ A) := by rw [e4, mul_one]
    _ = A * (PositivityTheory.GramSchwartzFunctions.EC.cT σ B * Dd) * PositivityTheory.GramSchwartzFunctions.EC.cT σ A := by
        simp only [Matrix.mul_assoc]
    _ = (A * PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd) * B * PositivityTheory.GramSchwartzFunctions.EC.cT σ A := by
        rw [e3]; simp only [Matrix.mul_assoc]
    _ = B * PositivityTheory.GramSchwartzFunctions.EC.cT σ A := by rw [e5, one_mul]

/- English proof (translation)
Introduce `K _ σ hσ n ρ p hn a b c d a₂ b₂ c₂ d₂ A B Dd hU hs ζ η hζ`. Take `⟨e4, e6⟩` from `siegel_relations σ hσ hU`. Rewrite `hs` using `[blkMul]`. Take `⟨rfl, rfl, rfl, rfl⟩` from `blkInj hs`. Use `⟨ζ + η * B * PositivityTheory.GramSchwartzFunctions.EC.cT σ (η * A), η * A, bl hn 1 (-(η * B)) 0 Dd, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[cTAdd, hζ, cTMul, cTInvol σ hσ, cTMul σ η B]`. Use `congr 1`. Rewrite using `[cTMul σ η A]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e6]`.

Simplify using `only [Matrix.mul_assoc]`. Simplify using `only [rowC, blMul]`. Use `congr 1`. Simplify using the standard rewrite rules. Simplify using `[Matrix.mul_add, Matrix.mul_assoc, add_comm]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using `only [rowD, blMul]`. Establish `e7 : Dd * PositivityTheory.GramSchwartzFunctions.EC.cT σ (η * A) = PositivityTheory.GramSchwartzFunctions.EC.cT σ η`. Rewrite using `[cTMul, ← Matrix.mul_assoc, e4, Matrix.one_mul]`.

Use `congr 1`. Simplify using `[Matrix.mul_assoc]`. Simplify using `[Matrix.mul_add, Matrix.mul_assoc, add_comm]`. Simplify using `[e7]`. Simplify using the standard rewrite rules.
-/
theorem exists_change_rep : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d a₂ b₂ c₂ d₂ A B Dd : Matrix (Fin p) (Fin p) K),
    IsUnitary σ (blk4 0 1 (-1) 0) (blk4 A B 0 Dd) → blk4 a b c d = blk4 A B 0 Dd * blk4 a₂ b₂ c₂ d₂ →
    ∀ (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K), cT σ ζ = ζ →
    ∃ (ζ₂ : Matrix (Fin ρ) (Fin ρ) K) (η₂ : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
      cT σ ζ₂ = ζ₂ ∧ rowC hn η a c = T * rowC hn η₂ a₂ c₂ ∧ rowD hn σ ζ η b d = T * rowD hn σ ζ₂ η₂ b₂ d₂ := by
  intro K _ σ hσ n ρ p hn a b c d a₂ b₂ c₂ d₂ A B Dd hU hs ζ η hζ
  obtain ⟨e4, e6⟩ := siegel_relations σ hσ hU
  rw [blkMul] at hs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := blkInj hs
  refine ⟨ζ + η * B * PositivityTheory.GramSchwartzFunctions.EC.cT σ (η * A), η * A, bl hn 1 (-(η * B)) 0 Dd, ?_, ?_, ?_⟩
  · rw [cTAdd, hζ, cTMul, cTInvol σ hσ, cTMul σ η B]
    congr 1
    rw [cTMul σ η A]
    calc η * A * (PositivityTheory.GramSchwartzFunctions.EC.cT σ B * PositivityTheory.GramSchwartzFunctions.EC.cT σ η)
        = η * (A * PositivityTheory.GramSchwartzFunctions.EC.cT σ B) * PositivityTheory.GramSchwartzFunctions.EC.cT σ η := by simp only [Matrix.mul_assoc]
      _ = η * B * (PositivityTheory.GramSchwartzFunctions.EC.cT σ A * PositivityTheory.GramSchwartzFunctions.EC.cT σ η) := by
          rw [e6]; simp only [Matrix.mul_assoc]
  · simp only [rowC, blMul]
    congr 1
    · simp
    · simp [Matrix.mul_add, Matrix.mul_assoc, add_comm]
    · simp
    · simp
  · simp only [rowD, blMul]
    have e7 : Dd * PositivityTheory.GramSchwartzFunctions.EC.cT σ (η * A) = PositivityTheory.GramSchwartzFunctions.EC.cT σ η := by
      rw [cTMul, ← Matrix.mul_assoc, e4, Matrix.one_mul]
    congr 1
    · simp [Matrix.mul_assoc]
    · simp [Matrix.mul_add, Matrix.mul_assoc, add_comm]
    · simp [e7]
    · simp

end GlobalTheory.CompanionTheory.ZUnf.ClassRep
