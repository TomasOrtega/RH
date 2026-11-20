import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut

noncomputable section

open Matrix Filter Topology Set
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma JJ_mul_JJ (n : ℕ) : JJ n * JJ n = -1 := by
  simp only [JJ, fromBlocks_multiply]
  rw [← fromBlocks_one, fromBlocks_neg]
  congr 1 <;> simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma det_JJ_ne (n : ℕ) : (JJ n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (JJ_mul_JJ n)
  rw [det_mul, h, zero_mul, det_neg, det_one] at this
  simp at this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Supply the required witnesses or components. A detailed English derivation is pending.
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
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma InG_JJ_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (JJ n * nU b) := by
  show (JJ n * nU b)ᴴ * JJ n * (JJ n * nU b) = JJ n
  simp [JJ, nU, fromBlocks_multiply, fromBlocks_conjTranspose, hb.eq]

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma InG_lower (s : ℝ) : InG (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1) := by
  show (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1)ᴴ * JJ n *
    fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1 = JJ n
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma lowerDiagonalBlockAsGL {M : M2 n} (h : InG M) : M.toBlocks₂₁ * M.toBlocks₂₂ᴴ = M.toBlocks₂₂ * M.toBlocks₂₁ᴴ := by
  have h2 := congrArg toBlocks₂₂ (yJyH h)
  rw [← fromBlocks_toBlocks M] at h2
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at h2
  exact (neg_add_eq_zero.mp h2).symm

end PositivityTheory.Rg.Sw.AbsSt.SZ
