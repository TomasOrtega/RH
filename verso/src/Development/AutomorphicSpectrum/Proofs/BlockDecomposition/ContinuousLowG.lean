import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData

noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.BigCell

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def lowU (t : ℝ) : M2 n := fromBlocks 1 0 ((t : ℂ) • 1) 1

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem lowU_mul (s t : ℝ) : (lowU s : M2 n) * lowU t = lowU (s + t) := by
  simp [lowU, fromBlocks_multiply, add_smul, add_comm]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem lowU_zero : (lowU 0 : M2 n) = 1 := by
  simp [lowU, fromBlocks_one]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem lowU_inG (t : ℝ) : InG (lowU t : M2 n) := by
  simp [InG, lowU, JJ, fromBlocks_conjTranspose, fromBlocks_multiply]

def lowG (t : ℝ) : GR n :=
  ⟨⟨lowU t, lowU (-t), by simp [lowU_mul, lowU_zero], by simp [lowU_mul, lowU_zero]⟩, lowU_inG t⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lowG_zero : (lowG 0 : GR n) = 1 :=
  Subtype.ext (Units.ext lowU_zero)

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem continuous_lowU : Continuous (lowU : ℝ → M2 n) := by
  unfold lowU
  exact Continuous.matrix_fromBlocks continuous_const continuous_const
    (Complex.continuous_ofReal.smul continuous_const) continuous_const

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem continuous_lowG : Continuous (lowG : ℝ → GR n) := by
  have h : Continuous (fun t : ℝ => ((lowG t : GR n) : GL (Fin n ⊕ Fin n) ℂ)) :=
    Units.continuous_iff.2 ⟨(continuous_lowU : Continuous (lowU : ℝ → M2 n)),
      ((continuous_lowU : Continuous (lowU : ℝ → M2 n)).comp continuous_neg)⟩
  exact h.subtype_mk _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

/- English proof (translation)
Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mul_JJ_mul_conj {M : M2 n} (h : InG M) : M * JJ n * Mᴴ = JJ n := by
  have h1 : (JJ n * Mᴴ * JJ n) * M = -1 := by
    calc (JJ n * Mᴴ * JJ n) * M = JJ n * (Mᴴ * JJ n * M) := by simp only [Matrix.mul_assoc]
      _ = -1 := by rw [h, JJ_mul_JJ]
  have h2 : (-(JJ n * Mᴴ * JJ n)) * M = 1 := by rw [Matrix.neg_mul, h1, neg_neg]
  have h3 : M * (-(JJ n * Mᴴ * JJ n)) = 1 := mul_eq_one_comm.1 h2
  calc M * JJ n * Mᴴ = (M * (-(JJ n * Mᴴ * JJ n))) * JJ n := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, JJ_mul_JJ]
        simp
    _ = JJ n := by rw [h3, Matrix.one_mul]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem lower_symm {A B C D : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks A B C D)) :
    C * Dᴴ = D * Cᴴ := by
  have := congrArg toBlocks₂₂ (mul_JJ_mul_conj h)
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at this
  exact (neg_add_eq_zero.1 this).symm

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Apply the first step, then apply the next step to every resulting obligation. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Apply function extensionality and compare values at an arbitrary argument. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem det_lower_I_ne (y : GR n) :
    ((mR y).toBlocks₂₁ + Complex.I • (mR y).toBlocks₂₂).det ≠ 0 := by
  set C := (mR y).toBlocks₂₁ with hC
  set D := (mR y).toBlocks₂₂ with hD
  have hM : InG (fromBlocks (mR y).toBlocks₁₁ (mR y).toBlocks₁₂ C D) := by
    rw [hC, hD, fromBlocks_toBlocks]; exact y.2
  have hs : C * Dᴴ = D * Cᴴ := lower_symm hM
  intro h0
  obtain ⟨v, hv, hvE⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  have hEE : (C + Complex.I • D) * (C + Complex.I • D)ᴴ = fromCols C D * (fromCols C D)ᴴ := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]
    simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, hs, smul_smul, Complex.star_def, Complex.conj_I]
    simp
    abel_nf
    simp [smul_smul]
  have hL : v ᵥ* fromCols C D = 0 := by
    rw [← Matrix.vecMul_self_mul_conjTranspose_eq_zero, ← hEE, ← Matrix.vecMul_vecMul, hvE,
      Matrix.zero_vecMul]
  have hw : (Sum.elim (0 : Fin n → ℂ) v) ᵥ* mR y = 0 := by
    funext j
    have := congrFun hL j
    rcases j with j | j <;>
      simpa [vecMul, dotProduct, Fintype.sum_sum_type, C, D, toBlocks₂₁, toBlocks₂₂] using this
  have hdet : (mR y).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero y.1
  have := Matrix.eq_zero_of_vecMul_eq_zero hdet hw
  apply hv
  funext i
  simpa using congrFun this (Sum.inr i)

def detPoly (C D : Matrix (Fin n) (Fin n) ℂ) : Polynomial ℂ :=
  (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C).det

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_detPoly (C D : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    (detPoly C D).eval z = (C + z • D).det := by
  have := (Polynomial.evalRingHom z).map_det
    (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C)
  rw [detPoly, ← Polynomial.coe_evalRingHom, this]
  congr 1
  ext i j
  simp
  ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem lower_mul_lowG (y : GR n) (t : ℝ) :
    (mR (y * lowG t)).toBlocks₂₁ = (mR y).toBlocks₂₁ + (t : ℂ) • (mR y).toBlocks₂₂ := by
  have h : mR (y * lowG t) = mR y * lowU t := rfl
  rw [h]
  conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
  simp [lowU, fromBlocks_multiply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem dense_bigCell : ∀ n : ℕ, Dense {y : GR n | ((mR y).toBlocks₂₁).det ≠ 0} := by
  intro n y
  have hP : detPoly (mR y).toBlocks₂₁ (mR y).toBlocks₂₂ ≠ 0 := by
    intro h
    apply det_lower_I_ne y
    rw [← eval_detPoly, h, Polynomial.eval_zero]
  have hfin : {t : ℝ | (detPoly (mR y).toBlocks₂₁ (mR y).toBlocks₂₂).eval (t : ℂ) = 0}.Finite :=
    (Polynomial.finite_setOf_isRoot hP).preimage Complex.ofReal_injective.injOn
  have hcl : IsClosed ({t : ℝ | (detPoly (mR y).toBlocks₂₁ (mR y).toBlocks₂₂).eval (t : ℂ) = 0} \ {0}) :=
    (hfin.subset Set.diff_subset).isClosed
  have hnh := hcl.isOpen_compl.mem_nhds (x := (0 : ℝ)) (by simp)
  have ht : Tendsto (fun t : ℝ => y * lowG t) (𝓝[≠] 0) (𝓝 y) := by
    have hc : Continuous (fun t : ℝ => y * lowG t) := continuous_const.mul continuous_lowG
    have := hc.tendsto 0
    simp only [lowG_zero, mul_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [nhdsWithin_le_nhds hnh, self_mem_nhdsWithin] with t h1 h2
  show ((mR (y * lowG t)).toBlocks₂₁).det ≠ 0
  rw [lower_mul_lowG, ← eval_detPoly]
  intro h3
  exact h1 ⟨h3, h2⟩

end GlobalTheory.CompanionTheory.BigCell
