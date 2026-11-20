import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut

noncomputable section

open Matrix Filter Topology Set
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

/- English proof (translation)
Simplify using `only [JJ, fromBlocks_multiply]`. Rewrite using `[← fromBlocks_one, fromBlocks_neg]`. Apply the tactic sequence `congr 1 <;> simp`.
-/
lemma JJ_mul_JJ (n : ℕ) : JJ n * JJ n = -1 := by
  simp only [JJ, fromBlocks_multiply]
  rw [← fromBlocks_one, fromBlocks_neg]
  congr 1 <;> simp

/- English proof (translation)
Introduce `h`. Use `congrArg Matrix.det (JJ_mul_JJ n)` as an intermediate fact. Rewrite `this` using `[det_mul, h, zero_mul, det_neg, det_one]`. Simplify using `at this`.
-/
lemma det_JJ_ne (n : ℕ) : (JJ n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (JJ_mul_JJ n)
  rw [det_mul, h, zero_mul, det_neg, det_one] at this
  simp at this

/- English proof (translation)
Establish `h' : Mᴴ * JJ n * M = JJ n` using `h`. Establish `hdet : M.det ≠ 0`. Introduce `h0`. Establish `hd` using `congrArg det h'`. Rewrite `hd` using `[det_mul, det_mul, h0, mul_zero]`.

Conclude with `det_JJ_ne n hd.symm`. Conclude with `⟨⟨GeneralLinearGroup.mkOfDetNeZero M hdet, h⟩, rfl⟩`.
-/
lemma exists_of_InG {M : M2 n} (h : InG M) : ∃ g : GR n, mR g = M := by
  have h' : Mᴴ * JJ n * M = JJ n := h
  have hdet : M.det ≠ 0 := by
    intro h0
    have hd := congrArg det h'
    rw [det_mul, det_mul, h0, mul_zero] at hd
    exact det_JJ_ne n hd.symm
  exact ⟨⟨GeneralLinearGroup.mkOfDetNeZero M hdet, h⟩, rfl⟩

/- English proof (translation)
Use `show (JJ n * nU b)ᴴ * JJ n * (JJ n * nU b) = JJ n`. Simplify using `[JJ, nU, fromBlocks_multiply, fromBlocks_conjTranspose, hb.eq]`.
-/
lemma InG_JJ_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (JJ n * nU b) := by
  show (JJ n * nU b)ᴴ * JJ n * (JJ n * nU b) = JJ n
  simp [JJ, nU, fromBlocks_multiply, fromBlocks_conjTranspose, hb.eq]

/- English proof (translation)
Use `show (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1)ᴴ * JJ n * fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1 = JJ n`. Simplify using `[JJ, fromBlocks_multiply, fromBlocks_conjTranspose]`.
-/
lemma InG_lower (s : ℝ) : InG (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1) := by
  show (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1)ᴴ * JJ n *
    fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1 = JJ n
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose]

/- English proof (translation)
Establish `h' : Mᴴ * JJ n * M = JJ n` using `h`. Establish `hJ` using `JJ_mul_JJ n`. Establish `h1 : (-(JJ n * Mᴴ * JJ n)) * M = 1`. Establish `e : (-(JJ n * Mᴴ * JJ n)) * M = -(JJ n * (Mᴴ * JJ n * M))`. Simplify using `[Matrix.mul_assoc]`.

Rewrite using `[e, h', hJ, neg_neg]`. Establish `h2` using `mul_eq_one_comm.mpr h1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[Matrix.mul_assoc, hJ]`. Use `_ = JJ n := by rw [h2, Matrix.one_mul]`.
-/
lemma yJyH {M : M2 n} (h : InG M) : M * JJ n * Mᴴ = JJ n := by
  have h' : Mᴴ * JJ n * M = JJ n := h
  have hJ := JJ_mul_JJ n
  have h1 : (-(JJ n * Mᴴ * JJ n)) * M = 1 := by
    have e : (-(JJ n * Mᴴ * JJ n)) * M = -(JJ n * (Mᴴ * JJ n * M)) := by
      simp [Matrix.mul_assoc]
    rw [e, h', hJ, neg_neg]
  have h2 := mul_eq_one_comm.mpr h1
  calc M * JJ n * Mᴴ = (M * (-(JJ n * Mᴴ * JJ n))) * JJ n := by
        simp [Matrix.mul_assoc, hJ]
    _ = JJ n := by rw [h2, Matrix.one_mul]

/- English proof (translation)
Establish `h2` using `congrArg toBlocks₂₂ (yJyH h)`. Rewrite `h2` using `[← fromBlocks_toBlocks M]`. Simplify using `[JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at h2`. Conclude with `(neg_add_eq_zero.mp h2).symm`.
-/
lemma lowerDiagonalBlockAsGL {M : M2 n} (h : InG M) : M.toBlocks₂₁ * M.toBlocks₂₂ᴴ = M.toBlocks₂₂ * M.toBlocks₂₁ᴴ := by
  have h2 := congrArg toBlocks₂₂ (yJyH h)
  rw [← fromBlocks_toBlocks M] at h2
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at h2
  exact (neg_add_eq_zero.mp h2).symm

end PositivityTheory.Rg.Sw.AbsSt.SZ
