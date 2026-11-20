import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompS

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[Cm, CmI, Matrix.mul_smul, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj]`. Simplify using `[smul_smul]`. Establish `h : -(Complex.I * 2⁻¹ * Complex.I + Complex.I * 2⁻¹ * Complex.I) = 1`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← neg_add, ← add_smul, ← neg_smul, h, one_smul]`.
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
Rewrite using `[Cm, CmI, Matrix.smul_mul, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj]`. Simplify using `[smul_smul]`. Establish `h : -(Complex.I * 2⁻¹ * Complex.I + Complex.I * 2⁻¹ * Complex.I) = 1`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← neg_add, ← add_smul, ← neg_smul, h, one_smul]`.
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
The claim follows from `Matrix.inv_eq_right_inv cm_mul_cmI`.
-/
theorem cm_inv : (Cm n)⁻¹ = CmI n := Matrix.inv_eq_right_inv cm_mul_cmI

/- English proof (translation)
Rewrite using `[Cm, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]`. Simplify using `[smul_smul]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← neg_add, ← add_smul, two_mul]`. Rewrite using `[← add_smul, two_mul]`.
-/
theorem cmH_JJ_cm : (Cm n)ᴴ * JJ n * Cm n = fromBlocks ((-(2 * Complex.I)) • 1) 0 0 ((2 * Complex.I) • 1) := by
  rw [Cm, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  simp [smul_smul]
  refine ⟨?_, ?_⟩
  · rw [← neg_add, ← add_smul, two_mul]
  · rw [← add_smul, two_mul]

end PositivityTheory.Rg.Sw.LVs.TC
