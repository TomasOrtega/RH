import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MultiplicityOneTestOperatorsAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulInverseCayley
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.InGBlocks

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem JJ_sq : JJ n * JJ n = -1 := by
  simp only [JJ, fromBlocks_multiply]
  rw [← fromBlocks_one, fromBlocks_neg]
  simp

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.
-/
theorem inv_of_inG {x : M2 n} (hx : InG x) : x⁻¹ = -(JJ n * xᴴ * JJ n) := by
  refine Matrix.inv_eq_left_inv ?_
  have h : xᴴ * JJ n * x = JJ n := hx
  calc -(JJ n * xᴴ * JJ n) * x = -(JJ n * (xᴴ * JJ n * x)) := by noncomm_ring
    _ = 1 := by rw [h, JJ_sq]; simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem isUnit_of_inG {x : M2 n} (hx : InG x) : IsUnit x := by
  have h : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    have h : xᴴ * JJ n * x = JJ n := hx
    calc -(JJ n * xᴴ * JJ n) * x = -(JJ n * (xᴴ * JJ n * x)) := by noncomm_ring
      _ = 1 := by rw [h, JJ_sq]; simp
  exact (Matrix.isUnit_iff_isUnit_det x).mpr (Matrix.isUnit_det_of_left_inverse h)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isUnit_det_of_inG {x : M2 n} (hx : InG x) : IsUnit x.det :=
  (Matrix.isUnit_iff_isUnit_det x).mp (isUnit_of_inG hx)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. A detailed English derivation is pending.
-/
theorem inverse_first_block_eq_conjTranspose {x : M2 n} (hx : InG x) : ub1 x = (u1 x)ᴴ := by
  rw [ub1, inv_of_inG hx, u1]
  conv_lhs => rw [← fromBlocks_toBlocks x]
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₂₁]
  simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, sub_eq_add_neg]
  abel

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem det_first_block_ne_zero_group {x : M2 n} (hx : InG x) : (u1 x).det ≠ 0 := by
  have := PositivityTheory.Rg.Sw.AbsSt.IwaPf.det_ne x hx Complex.I (by simp [Complex.ext_iff]; norm_num)
  simpa [u1] using this

def Nq (Q : Matrix (Fin n) (Fin n) ℂ) : M2 n := Cm n * fromBlocks 0 Q 0 0 * Cmi n

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cmi_mul_cm : Cmi n * Cm n = 1 := mul_eq_one_comm.mp cm_mul_cmi

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem Nq_sq (Q : Matrix (Fin n) (Fin n) ℂ) : Nq Q * Nq Q = 0 := by
  have : fromBlocks 0 Q 0 0 * fromBlocks 0 Q 0 0 = (0 : M2 n) := by
    rw [fromBlocks_multiply]; simp [fromBlocks_zero]
  calc Nq Q * Nq Q = Cm n * fromBlocks 0 Q 0 0 * (Cmi n * Cm n) * fromBlocks 0 Q 0 0 * Cmi n := by
        simp only [Nq, Matrix.mul_assoc]
    _ = 0 := by rw [cmi_mul_cm, Matrix.mul_one, Matrix.mul_assoc (Cm n), this]; simp

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.
-/
theorem mX_eq (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : mX (1 : Matrix (Fin n) (Fin n) ℂ) (s • Q) 0 1 = 1 + s • Nq Q := by
  have e : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (s • Q) 0 1 : M2 n) = 1 + s • (fromBlocks 0 Q 0 0 : M2 n) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
  rw [mX, cm_inv, e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, cm_mul_cmi, Nq, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem lowQ_eq (Q : Matrix (Fin n) (Fin n) ℂ) : lowQ Q = Nq Q := by
  have := mX_eq Q 1
  rw [one_smul, one_smul] at this
  rw [lowQ, this]; abel

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem Nq_blocks (Q : Matrix (Fin n) (Fin n) ℂ) :
    Nq Q = fromBlocks (-(1 / 2 : ℂ) • Q) ((Complex.I / 2) • Q) ((Complex.I / 2) • Q) ((1 / 2 : ℂ) • Q) := by
  rw [Nq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem inv_mul_lower {x : M2 n} (hx : IsUnit x) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    (x * (1 + s • Nq Q))⁻¹ = (1 - s • Nq Q) * x⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  have hN := Nq_sq Q
  have e : (1 + s • Nq Q) * (1 - s • Nq Q) = (1 : M2 n) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hN]
    simp
  have hx' : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv x ((Matrix.isUnit_iff_isUnit_det x).mp hx)
  calc x * (1 + s • Nq Q) * ((1 - s • Nq Q) * x⁻¹) = x * ((1 + s • Nq Q) * (1 - s • Nq Q)) * x⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [e, Matrix.mul_one, hx']

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem upper_left_block_sub (A B : M2 n) : (A - B).toBlocks₁₁ = A.toBlocks₁₁ - B.toBlocks₁₁ := by ext; simp [toBlocks₁₁]
/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem lower_left_block_sub (A B : M2 n) : (A - B).toBlocks₂₁ = A.toBlocks₂₁ - B.toBlocks₂₁ := by ext; simp [toBlocks₂₁]
/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem upper_left_block_smul (c : ℂ) (A : M2 n) : (c • A).toBlocks₁₁ = c • A.toBlocks₁₁ := by ext; simp [toBlocks₁₁]
/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem lower_left_block_smul (c : ℂ) (A : M2 n) : (c • A).toBlocks₂₁ = c • A.toBlocks₂₁ := by ext; simp [toBlocks₂₁]
/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem upper_left_block_mul_eq (A B : M2 n) : (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Put the polynomial expressions in normal form.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inverse_first_block_lowering {x : M2 n} (hx : IsUnit x) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    ub1 (x * (1 + s • Nq Q)) = ub1 x - s • (Q * ub2 x) := by
  rw [ub1, inv_mul_lower hx, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, upper_left_block_sub, lower_left_block_sub, upper_left_block_smul,
    lower_left_block_smul, upper_left_block_mul_eq, toBlocks₂₁_mul, Nq_blocks, ub1, ub2]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.smul_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul, smul_add, smul_sub, smul_neg, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem first_block_lowering_invariant (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : u1 (x * (1 + s • Nq Q)) = u1 x := by
  have := (uAct n x 1 (s • Q) 0 1).1
  rw [mX_eq] at this
  rw [this]; simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem det_lower (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : (x * (1 + s • Nq Q)).det = x.det := by
  rw [← mX_eq, det_mul, mX, cm_inv, det_mul, det_mul, det_fromBlocks_zero₂₁]
  have : (Cm n).det * (Cmi n).det = 1 := by rw [← det_mul, cm_mul_cmi, det_one]
  simp only [det_one, mul_one]
  linear_combination x.det * this

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative
