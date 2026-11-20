import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ConjugateTransposeDerivatives.TraceSingleMulSingle

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)
open Cxa

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cf_apply {n : ℕ} (H : Mat n) (m : Md n) : cf n H m = (((H * hbM m).trace.re : ℝ) : ℂ) := rfl

/- English proof (translation)
Rewrite using `[cf_apply]`. Conclude with `trace_re_of_herm hH (by rw [hbM_eq]; exact hb_herm _)`.
-/
private theorem cf_eq_trace_mul_hbM_of_isHermitian {n : ℕ} (H : Mat n) (hH : H.IsHermitian) (m : Md n) :
    cf n H m = (H * hbM m).trace := by
  rw [cf_apply]
  exact trace_re_of_herm hH (by rw [hbM_eq]; exact hb_herm _)

/- English proof (translation)
Introduce `n H hH`. Establish `key : ∀ p : Fin n × Fin n, trace ((H - ∑ m : Md n, cf n H m • hbM m) * hb p) = 0`. Introduce `p`. Rewrite using `[sub_mul, trace_sub, Finset.sum_mul, trace_sum]`. Repeatedly rewrite using `[smul_mul_assoc, trace_smul]`.

Rewrite using `[← finProdFinEquiv.sum_comp]`. Simplify using `only [hbM_eq, Equiv.symm_apply_apply, hb_ortho, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_ite_eq' Finset.univ p, if_pos (Finset.mem_univ _), cf_eq_trace_mul_hbM_of_isHermitian H hH, hbM_eq, Equiv.symm_apply_apply, sub_self]`. Conclude with `(sub_eq_zero.mp (eq_zero_of_trace _ key))`.
-/
theorem hbExp : HbExp := by
  intro n H hH
  have key : ∀ p : Fin n × Fin n, trace ((H - ∑ m : Md n, cf n H m • hbM m) * hb p) = 0 := by
    intro p
    rw [sub_mul, trace_sub, Finset.sum_mul, trace_sum]
    simp_rw [smul_mul_assoc, trace_smul]
    rw [← finProdFinEquiv.sum_comp]
    simp only [hbM_eq, Equiv.symm_apply_apply, hb_ortho, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ p, if_pos (Finset.mem_univ _), cf_eq_trace_mul_hbM_of_isHermitian H hH, hbM_eq,
      Equiv.symm_apply_apply, sub_self]
  exact (sub_eq_zero.mp (eq_zero_of_trace _ key))

/- English proof (translation)
Introduce `n H H' hH hH'`. Use `conv_rhs => rw [hbExp n H' hH']`. Rewrite using `[Matrix.mul_sum, trace_sum]`. Repeatedly rewrite using `[mul_smul_comm, trace_smul, smul_eq_mul]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[cf_eq_trace_mul_hbM_of_isHermitian H hH m, mul_comm]`.
-/
theorem cfPair : CfPair := by
  intro n H H' hH hH'
  conv_rhs => rw [hbExp n H' hH']
  rw [Matrix.mul_sum, trace_sum]
  simp_rw [mul_smul_comm, trace_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [cf_eq_trace_mul_hbM_of_isHermitian H hH m, mul_comm]

/- English proof (translation)
Establish `hM : ∀ r : Md n, (hbM r).IsHermitian` using `fun r => by rw [hbM_eq]; exact hb_herm _`. Rewrite using `[cf_eq_trace_mul_hbM_of_isHermitian _ (herm_sandwich x K hK) p]`. Use `conv_lhs => rw [hbExp n K hK]`. Rewrite using `[Matrix.mul_sum, Finset.sum_mul, Finset.sum_mul, trace_sum]`. Repeatedly rewrite using `[mul_smul_comm, smul_mul_assoc, trace_smul, smul_eq_mul]`.

Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[cf_eq_trace_mul_hbM_of_isHermitian _ (herm_sandwich x _ (hM r)) p]`.
-/
theorem cf_sandwich {n : ℕ} (x K : Mat n) (hK : K.IsHermitian) (p : Md n) :
    cf n (x * K * xᴴ) p = ∑ r, cf n K r * cf n (x * hbM r * xᴴ) p := by
  have hM : ∀ r : Md n, (hbM r).IsHermitian := fun r => by rw [hbM_eq]; exact hb_herm _
  rw [cf_eq_trace_mul_hbM_of_isHermitian _ (herm_sandwich x K hK) p]
  conv_lhs => rw [hbExp n K hK]
  rw [Matrix.mul_sum, Finset.sum_mul, Finset.sum_mul, trace_sum]
  simp_rw [mul_smul_comm, smul_mul_assoc, trace_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [cf_eq_trace_mul_hbM_of_isHermitian _ (herm_sandwich x _ (hM r)) p]

/- English proof (translation)
Introduce `n`. Establish `hM : ∀ r : Md n, (hbM r).IsHermitian` using `fun r => by rw [hbM_eq]; exact hb_herm _`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `p q show (cf n) (1 * hbM q * (1 : Mat n)ᴴ) p = (1 : Matrix (Md n) (Md n) ℂ) p q`. Rewrite using `[conjTranspose_one, Matrix.mul_one, Matrix.one_mul, cf_eq_trace_mul_hbM_of_isHermitian _ (hM q), hbM_eq, hbM_eq, hb_ortho, Matrix.one_apply]`.

Distinguish the cases in `h : p = q`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `h' : finProdFinEquiv.symm q ≠ finProdFinEquiv.symm p` using `fun e => h (finProdFinEquiv.symm.injective e).symm`. Rewrite using `[if_neg h', if_neg h]`.

Introduce `x y`. Use extensionality with `p q`. Rewrite using `[Matrix.mul_apply]`. Use `show (cf n) (x * y * hbM q * (x * y)ᴴ) p = ∑ r, (cf n) (x * hbM r * xᴴ) p * (cf n) (y * hbM q * yᴴ) r`. Establish `e : x * y * hbM q * (x * y)ᴴ = x * (y * hbM q * yᴴ) * xᴴ`.

Rewrite using `[conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, cf_sandwich x _ (herm_sandwich y _ (hM q)) p]`. Conclude with `Finset.sum_congr rfl fun r _ => mul_comm _ _`. Introduce `x H hH`.

Use extensionality with `p`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[cf_sandwich x H hH p]`. Conclude with `Finset.sum_congr rfl fun r _ => mul_comm _ _`. Introduce `x H hH`.

Use extensionality with `p`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]`. Establish `hs : (xᴴ * H * x).IsHermitian`. Use `herm_sandwich xᴴ H hH` as an intermediate fact. Rewrite `this` using `[conjTranspose_conjTranspose]`. Then use the resulting hypothesis.

Use `Eq.trans (cfPair n (x * hbM p * xᴴ) H (herm_sandwich _ _ (hM p)) hH) ?_` and prove the remaining obligations. Rewrite using `[cf_eq_trace_mul_hbM_of_isHermitian _ hs p, Matrix.mul_assoc (x * hbM p), trace_mul_comm (x * hbM p)]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem mtLaws : MtLaws := by
  intro n
  have hM : ∀ r : Md n, (hbM r).IsHermitian := fun r => by rw [hbM_eq]; exact hb_herm _
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext p q
    show (cf n) (1 * hbM q * (1 : Mat n)ᴴ) p = (1 : Matrix (Md n) (Md n) ℂ) p q
    rw [conjTranspose_one, Matrix.mul_one, Matrix.one_mul, cf_eq_trace_mul_hbM_of_isHermitian _ (hM q), hbM_eq, hbM_eq,
      hb_ortho, Matrix.one_apply]
    by_cases h : p = q
    · subst h
      simp
    · have h' : finProdFinEquiv.symm q ≠ finProdFinEquiv.symm p := fun e => h (finProdFinEquiv.symm.injective e).symm
      rw [if_neg h', if_neg h]
  · intro x y
    ext p q
    rw [Matrix.mul_apply]
    show (cf n) (x * y * hbM q * (x * y)ᴴ) p = ∑ r, (cf n) (x * hbM r * xᴴ) p * (cf n) (y * hbM q * yᴴ) r
    have e : x * y * hbM q * (x * y)ᴴ = x * (y * hbM q * yᴴ) * xᴴ := by
      rw [conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [e, cf_sandwich x _ (herm_sandwich y _ (hM q)) p]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  · intro x H hH
    ext p
    simp only [Matrix.mulVec, dotProduct]
    rw [cf_sandwich x H hH p]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  · intro x H hH
    ext p
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    have hs : (xᴴ * H * x).IsHermitian := by
      have := herm_sandwich xᴴ H hH
      rwa [conjTranspose_conjTranspose] at this
    refine Eq.trans (cfPair n (x * hbM p * xᴴ) H (herm_sandwich _ _ (hM p)) hH) ?_
    rw [cf_eq_trace_mul_hbM_of_isHermitian _ hs p, Matrix.mul_assoc (x * hbM p), trace_mul_comm (x * hbM p)]
    simp only [Matrix.mul_assoc]

end PositivityTheory.RgBcC
