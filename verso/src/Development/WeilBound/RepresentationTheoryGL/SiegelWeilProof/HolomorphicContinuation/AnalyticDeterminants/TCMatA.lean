import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompS

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Put the polynomial expressions in normal form. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.
-/
theorem cm_mul_cmI : Cm n * CmI n = 1 := by
  rw [Cm, CmI, Matrix.mul_smul, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj]
  simp [smul_smul]
  have h : -(Complex.I * 2⁻¹ * Complex.I + Complex.I * 2⁻¹ * Complex.I) = 1 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← neg_add, ← add_smul, ← neg_smul, h, one_smul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Put the polynomial expressions in normal form. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.
-/
theorem cmI_mul_cm : CmI n * Cm n = 1 := by
  rw [Cm, CmI, Matrix.smul_mul, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj]
  simp [smul_smul]
  have h : -(Complex.I * 2⁻¹ * Complex.I + Complex.I * 2⁻¹ * Complex.I) = 1 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← neg_add, ← add_smul, ← neg_smul, h, one_smul]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cm_inv : (Cm n)⁻¹ = CmI n := Matrix.inv_eq_right_inv cm_mul_cmI

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem cmH_JJ_cm : (Cm n)ᴴ * JJ n * Cm n = fromBlocks ((-(2 * Complex.I)) • 1) 0 0 ((2 * Complex.I) • 1) := by
  rw [Cm, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  simp [smul_smul]
  refine ⟨?_, ?_⟩
  · rw [← neg_add, ← add_smul, two_mul]
  · rw [← add_smul, two_mul]

end PositivityTheory.Rg.Sw.LVs.TC
