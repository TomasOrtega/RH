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
Simplify using `[lowU, fromBlocks_multiply, add_smul, add_comm]`.
-/
theorem lowU_mul (s t : ℝ) : (lowU s : M2 n) * lowU t = lowU (s + t) := by
  simp [lowU, fromBlocks_multiply, add_smul, add_comm]

/- English proof (translation)
Simplify using `[lowU, fromBlocks_one]`.
-/
theorem lowU_zero : (lowU 0 : M2 n) = 1 := by
  simp [lowU, fromBlocks_one]

/- English proof (translation)
Simplify using `[InG, lowU, JJ, fromBlocks_conjTranspose, fromBlocks_multiply]`.
-/
theorem lowU_inG (t : ℝ) : InG (lowU t : M2 n) := by
  simp [InG, lowU, JJ, fromBlocks_conjTranspose, fromBlocks_multiply]

def lowG (t : ℝ) : GR n :=
  ⟨⟨lowU t, lowU (-t), by simp [lowU_mul, lowU_zero], by simp [lowU_mul, lowU_zero]⟩, lowU_inG t⟩

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext lowU_zero)`.
-/
theorem lowG_zero : (lowG 0 : GR n) = 1 :=
  Subtype.ext (Units.ext lowU_zero)

/- English proof (translation)
Unfold `lowU`. Conclude with `Continuous.matrix_fromBlocks continuous_const continuous_const (Complex.continuous_ofReal.smul continuous_const) continuous_const`.
-/
theorem continuous_lowU : Continuous (lowU : ℝ → M2 n) := by
  unfold lowU
  exact Continuous.matrix_fromBlocks continuous_const continuous_const
    (Complex.continuous_ofReal.smul continuous_const) continuous_const

/- English proof (translation)
Establish `h : Continuous (fun t : ℝ => ((lowG t : GR n) : GL (Fin n ⊕ Fin n) ℂ))` using `Units.continuous_iff.2 ⟨(continuous_lowU : Continuous (lowU : ℝ → M2 n)), ((continuous_lowU : Continuous (lowU : ℝ → M2 n)).comp continuous_neg)⟩`. Conclude with `h.subtype_mk _`.
-/
theorem continuous_lowG : Continuous (lowG : ℝ → GR n) := by
  have h : Continuous (fun t : ℝ => ((lowG t : GR n) : GL (Fin n ⊕ Fin n) ℂ)) :=
    Units.continuous_iff.2 ⟨(continuous_lowU : Continuous (lowU : ℝ → M2 n)),
      ((continuous_lowU : Continuous (lowU : ℝ → M2 n)).comp continuous_neg)⟩
  exact h.subtype_mk _

/- English proof (translation)
Rewrite using `[JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]`. Simplify using the standard rewrite rules.
-/
theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

/- English proof (translation)
Establish `h1 : (JJ n * Mᴴ * JJ n) * M = -1`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : (-(JJ n * Mᴴ * JJ n)) * M = 1` using `by rw [Matrix.neg_mul, h1, neg_neg]`. Establish `h3 : M * (-(JJ n * Mᴴ * JJ n)) = 1` using `mul_eq_one_comm.1 h2`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, JJ_mul_JJ]`. Simplify using the standard rewrite rules. Use `_ = JJ n := by rw [h3, Matrix.one_mul]`.
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
Use `congrArg toBlocks₂₂ (mul_JJ_mul_conj h)` as an intermediate fact. Simplify using `[JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at this`. Conclude with `(neg_add_eq_zero.1 this).symm`.
-/
theorem lower_symm {A B C D : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks A B C D)) :
    C * Dᴴ = D * Cᴴ := by
  have := congrArg toBlocks₂₂ (mul_JJ_mul_conj h)
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at this
  exact (neg_add_eq_zero.1 this).symm

/- English proof (translation)
Use `set C := (mR y).toBlocks₂₁ with hC`. Use `set D := (mR y).toBlocks₂₂ with hD`. Establish `hM : InG (fromBlocks (mR y).toBlocks₁₁ (mR y).toBlocks₁₂ C D)`. Rewrite using `[hC, hD, fromBlocks_toBlocks]`. Conclude with `y.2`.

Establish `hs : C * Dᴴ = D * Cᴴ` using `lower_symm hM`. Introduce `h0`. Take `⟨v, hv, hvE⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 h0`. Establish `hEE : (C + Complex.I • D) * (C + Complex.I • D)ᴴ = fromCols C D * (fromCols C D)ᴴ`. Rewrite using `[conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]`.

Simplify using `only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hs, smul_smul, Complex.star_def, Complex.conj_I]`. Simplify using the standard rewrite rules. Use `abel_nf`. Simplify using `[smul_smul]`. Establish `hL : v ᵥ* fromCols C D = 0`.

Rewrite using `[← Matrix.vecMul_self_mul_conjTranspose_eq_zero, ← hEE, ← Matrix.vecMul_vecMul, hvE, Matrix.zero_vecMul]`. Establish `hw : (Sum.elim (0 : Fin n → ℂ) v) ᵥ* mR y = 0`. Use function extensionality and compare the values at `j`. Use `congrFun hL j` as an intermediate fact. Apply the tactic sequence `rcases j with j | j <;>`.

Simplify `this` using `[vecMul, dotProduct, Fintype.sum_sum_type, C, D, toBlocks₂₁, toBlocks₂₂]`. Establish `hdet : (mR y).det ≠ 0` using `Matrix.GeneralLinearGroup.det_ne_zero y.1`. Use `Matrix.eq_zero_of_vecMul_eq_zero hdet hw` as an intermediate fact. Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Simplify using `using congrFun this (Sum.inr i)`.
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
Use `(Polynomial.evalRingHom z).map_det (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C)` as an intermediate fact. Rewrite using `[detPoly, ← Polynomial.coe_evalRingHom, this]`. Use `congr 1`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

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
Establish `h : mR (y * lowG t) = mR y * lowU t` using `rfl`. Rewrite using `[h]`. Use `conv_lhs => rw [← fromBlocks_toBlocks (mR y)]`. Simplify using `[lowU, fromBlocks_multiply]`.
-/
theorem lower_mul_lowG (y : GR n) (t : ℝ) :
    (mR (y * lowG t)).toBlocks₂₁ = (mR y).toBlocks₂₁ + (t : ℂ) • (mR y).toBlocks₂₂ := by
  have h : mR (y * lowG t) = mR y * lowU t := rfl
  rw [h]
  conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
  simp [lowU, fromBlocks_multiply]

/- English proof (translation)
Introduce `n y`. Establish `hP : detPoly (mR y).toBlocks₂₁ (mR y).toBlocks₂₂ ≠ 0`. Introduce `h`. Apply `det_lower_I_ne y` to reduce the goal to its premises. Rewrite using `[← eval_detPoly, h, Polynomial.eval_zero]`.

Establish `hfin : {t : ℝ | (detPoly (mR y).toBlocks₂₁ (mR y).toBlocks₂₂).eval (t : ℂ) = 0}.Finite` using `(Polynomial.finite_setOf_isRoot hP).preimage Complex.ofReal_injective.injOn`. Establish `hcl : IsClosed ({t : ℝ | (detPoly (mR y).toBlocks₂₁ (mR y).toBlocks₂₂).eval (t : ℂ) = 0} \ {0})` using `(hfin.subset Set.diff_subset).isClosed`. Establish `hnh` using `hcl.isOpen_compl.mem_nhds (x := (0 : ℝ)) (by simp)`. Establish `ht : Tendsto (fun t : ℝ => y * lowG t) (𝓝[≠] 0) (𝓝 y)`. Establish `hc : Continuous (fun t : ℝ => y * lowG t)` using `continuous_const.mul continuous_lowG`.

Use `hc.tendsto 0` as an intermediate fact. Simplify using `only [lowG_zero, mul_one] at this`. Conclude with `this.mono_left nhdsWithin_le_nhds`. Use `mem_closure_of_tendsto ht ?_` and prove the remaining obligations. Use `filter_upwards [nhdsWithin_le_nhds hnh, self_mem_nhdsWithin] with t h1 h2`.

Use `show ((mR (y * lowG t)).toBlocks₂₁).det ≠ 0`. Rewrite using `[lower_mul_lowG, ← eval_detPoly]`. Introduce `h3`. Conclude with `h1 ⟨h3, h2⟩`.
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
