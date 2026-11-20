import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MultiplicityOneTestOperatorsAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulInverseCayley
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.InGBlocks

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

/- English proof (translation)
Simplify using `only [JJ, fromBlocks_multiply]`. Rewrite using `[← fromBlocks_one, fromBlocks_neg]`. Simplify using the standard rewrite rules.
-/
theorem JJ_sq : JJ n * JJ n = -1 := by
  simp only [JJ, fromBlocks_multiply]
  rw [← fromBlocks_one, fromBlocks_neg]
  simp

/- English proof (translation)
Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Establish `h : xᴴ * JJ n * x = JJ n` using `hx`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_of_inG {x : M2 n} (hx : InG x) : x⁻¹ = -(JJ n * xᴴ * JJ n) := by
  refine Matrix.inv_eq_left_inv ?_
  have h : xᴴ * JJ n * x = JJ n := hx
  calc -(JJ n * xᴴ * JJ n) * x = -(JJ n * (xᴴ * JJ n * x)) := by noncomm_ring
    _ = 1 := by rw [h, JJ_sq]; simp

/- English proof (translation)
Establish `h : (-(JJ n * xᴴ * JJ n)) * x = 1`. Establish `h : xᴴ * JJ n * x = JJ n` using `hx`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(Matrix.isUnit_iff_isUnit_det x).mpr (Matrix.isUnit_det_of_left_inverse h)`.
-/
theorem isUnit_of_inG {x : M2 n} (hx : InG x) : IsUnit x := by
  have h : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    have h : xᴴ * JJ n * x = JJ n := hx
    calc -(JJ n * xᴴ * JJ n) * x = -(JJ n * (xᴴ * JJ n * x)) := by noncomm_ring
      _ = 1 := by rw [h, JJ_sq]; simp
  exact (Matrix.isUnit_iff_isUnit_det x).mpr (Matrix.isUnit_det_of_left_inverse h)

/- English proof (translation)
The claim follows from `(Matrix.isUnit_iff_isUnit_det x).mp (isUnit_of_inG hx)`.
-/
theorem isUnit_det_of_inG {x : M2 n} (hx : InG x) : IsUnit x.det :=
  (Matrix.isUnit_iff_isUnit_det x).mp (isUnit_of_inG hx)

/- English proof (translation)
Rewrite using `[ub1, inv_of_inG hx, u1]`. Use `conv_lhs => rw [← fromBlocks_toBlocks x]`. Simplify using `only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁]`. Simplify using `[Matrix.conjTranspose_add, Matrix.conjTranspose_smul, sub_eq_add_neg]`. Normalize the expressions using the abelian group laws.
-/
theorem inverse_first_block_eq_conjTranspose {x : M2 n} (hx : InG x) : ub1 x = (u1 x)ᴴ := by
  rw [ub1, inv_of_inG hx, u1]
  conv_lhs => rw [← fromBlocks_toBlocks x]
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₂₁]
  simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, sub_eq_add_neg]
  abel

/- English proof (translation)
Use `PositivityTheory.Rg.Sw.AbsSt.IwaPf.det_ne x hx Complex.I (by simp [Complex.ext_iff]; norm_num)` as an intermediate fact. Simplify `this` using `[u1]`.
-/
theorem det_first_block_ne_zero_group {x : M2 n} (hx : InG x) : (u1 x).det ≠ 0 := by
  have := PositivityTheory.Rg.Sw.AbsSt.IwaPf.det_ne x hx Complex.I (by simp [Complex.ext_iff]; norm_num)
  simpa [u1] using this

def Nq (Q : Matrix (Fin n) (Fin n) ℂ) : M2 n := Cm n * fromBlocks 0 Q 0 0 * Cmi n

/- English proof (translation)
The claim follows from `mul_eq_one_comm.mp cm_mul_cmi`.
-/
theorem cmi_mul_cm : Cmi n * Cm n = 1 := mul_eq_one_comm.mp cm_mul_cmi

/- English proof (translation)
Establish `: fromBlocks 0 Q 0 0 * fromBlocks 0 Q 0 0 = (0 : M2 n)`. Rewrite using `[fromBlocks_multiply]`. Simplify using `[fromBlocks_zero]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Nq, Matrix.mul_assoc]`.

Use `_ = 0 := by rw [cmi_mul_cm, Matrix.mul_one, Matrix.mul_assoc (Cm n), this]; simp`.
-/
theorem Nq_sq (Q : Matrix (Fin n) (Fin n) ℂ) : Nq Q * Nq Q = 0 := by
  have : fromBlocks 0 Q 0 0 * fromBlocks 0 Q 0 0 = (0 : M2 n) := by
    rw [fromBlocks_multiply]; simp [fromBlocks_zero]
  calc Nq Q * Nq Q = Cm n * fromBlocks 0 Q 0 0 * (Cmi n * Cm n) * fromBlocks 0 Q 0 0 * Cmi n := by
        simp only [Nq, Matrix.mul_assoc]
    _ = 0 := by rw [cmi_mul_cm, Matrix.mul_one, Matrix.mul_assoc (Cm n), this]; simp

/- English proof (translation)
Establish `e : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (s • Q) 0 1 : M2 n) = 1 + s • (fromBlocks 0 Q 0 0 : M2 n)`. Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]`. Rewrite using `[mX, cm_inv, e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, cm_mul_cmi, Nq, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem mX_eq (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : mX (1 : Matrix (Fin n) (Fin n) ℂ) (s • Q) 0 1 = 1 + s • Nq Q := by
  have e : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (s • Q) 0 1 : M2 n) = 1 + s • (fromBlocks 0 Q 0 0 : M2 n) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
  rw [mX, cm_inv, e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, cm_mul_cmi, Nq, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Use `mX_eq Q 1` as an intermediate fact. Rewrite `this` using `[one_smul, one_smul]`. Rewrite using `[lowQ, this]`. Normalize the expressions using the abelian group laws.
-/
theorem lowQ_eq (Q : Matrix (Fin n) (Fin n) ℂ) : lowQ Q = Nq Q := by
  have := mX_eq Q 1
  rw [one_smul, one_smul] at this
  rw [lowQ, this]; abel

/- English proof (translation)
Rewrite using `[Nq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]`. Apply the tactic sequence `congr 1 <;> ext i j <;> simp [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply] <;> ring_nf <;>`. Apply the tactic sequence `simp [Complex.I_sq] <;> ring`.
-/
theorem Nq_blocks (Q : Matrix (Fin n) (Fin n) ℂ) :
    Nq Q = fromBlocks (-(1 / 2 : ℂ) • Q) ((Complex.I / 2) • Q) ((Complex.I / 2) • Q) ((1 / 2 : ℂ) • Q) := by
  rw [Nq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

/- English proof (translation)
Use `Matrix.inv_eq_right_inv ?_` and prove the remaining obligations. Establish `hN` using `Nq_sq Q`. Establish `e : (1 + s • Nq Q) * (1 - s • Nq Q) = (1 : M2 n)`. Rewrite using `[Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hN]`. Simplify using the standard rewrite rules.

Establish `hx' : x * x⁻¹ = 1` using `Matrix.mul_nonsing_inv x ((Matrix.isUnit_iff_isUnit_det x).mp hx)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [e, Matrix.mul_one, hx']`.
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
Use `ext`. Simplify using `[toBlocks₁₁]`.
-/
theorem upper_left_block_sub (A B : M2 n) : (A - B).toBlocks₁₁ = A.toBlocks₁₁ - B.toBlocks₁₁ := by ext; simp [toBlocks₁₁]
/- English proof (translation)
Use `ext`. Simplify using `[toBlocks₂₁]`.
-/
theorem lower_left_block_sub (A B : M2 n) : (A - B).toBlocks₂₁ = A.toBlocks₂₁ - B.toBlocks₂₁ := by ext; simp [toBlocks₂₁]
/- English proof (translation)
Use `ext`. Simplify using `[toBlocks₁₁]`.
-/
theorem upper_left_block_smul (c : ℂ) (A : M2 n) : (c • A).toBlocks₁₁ = c • A.toBlocks₁₁ := by ext; simp [toBlocks₁₁]
/- English proof (translation)
Use `ext`. Simplify using `[toBlocks₂₁]`.
-/
theorem lower_left_block_smul (c : ℂ) (A : M2 n) : (c • A).toBlocks₂₁ = c • A.toBlocks₂₁ := by ext; simp [toBlocks₂₁]
/- English proof (translation)
Use `conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]`. Simplify using the standard rewrite rules.
-/
theorem upper_left_block_mul_eq (A B : M2 n) : (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

/- English proof (translation)
Rewrite using `[ub1, inv_mul_lower hx, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, upper_left_block_sub, lower_left_block_sub, upper_left_block_smul, lower_left_block_smul, upper_left_block_mul_eq, toBlocks₂₁_mul, Nq_blocks, ub1, ub2]`. Simplify using `only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul, smul_add, smul_sub, smul_neg, smul_smul]`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]`. Put the polynomial expressions in normal form.

Simplify using `only [Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
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
Use `(uAct n x 1 (s • Q) 0 1).1` as an intermediate fact. Rewrite `this` using `[mX_eq]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem first_block_lowering_invariant (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : u1 (x * (1 + s • Nq Q)) = u1 x := by
  have := (uAct n x 1 (s • Q) 0 1).1
  rw [mX_eq] at this
  rw [this]; simp

/- English proof (translation)
Rewrite using `[← mX_eq, det_mul, mX, cm_inv, det_mul, det_mul, det_fromBlocks_zero₂₁]`. Establish `: (Cm n).det * (Cmi n).det = 1` using `by rw [← det_mul, cm_mul_cmi, det_one]`. Simplify using `only [det_one, mul_one]`. Take the linear combination `x.det * this`.
-/
theorem det_lower (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : (x * (1 + s • Nq Q)).det = x.det := by
  rw [← mX_eq, det_mul, mX, cm_inv, det_mul, det_mul, det_fromBlocks_zero₂₁]
  have : (Cm n).det * (Cmi n).det = 1 := by rw [← det_mul, cm_mul_cmi, det_one]
  simp only [det_one, mul_one]
  linear_combination x.det * this

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative
