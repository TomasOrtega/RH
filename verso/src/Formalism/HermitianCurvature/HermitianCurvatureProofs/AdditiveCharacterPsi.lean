import Formalism.HermitianCurvature.StatementG

open Matrix MeasureTheory

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Formalism.FourierDecayAlt.P.G2

open Formalism.FourierDecayAlt.G

/- English proof (translation)
The claim follows from `finSumFinEquiv_symm_apply_castAdd (n := 1) i`.
-/
theorem symm_castSucc {n : ℕ} (i : Fin n) :
    finSumFinEquiv.symm (i.castSucc : Fin (n + 1)) = Sum.inl i :=
  finSumFinEquiv_symm_apply_castAdd (n := 1) i

/- English proof (translation)
The claim follows from `finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)`.
-/
theorem symm_last (n : ℕ) : finSumFinEquiv.symm (Fin.last n : Fin (n + 1)) = Sum.inr (0 : Fin 1) :=
  finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)

/- English proof (translation)
Simplify using `[blk, symm_castSucc]`.
-/
theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := by
  simp [blk, symm_castSucc]

/- English proof (translation)
Simplify using `[blk, symm_castSucc, symm_last]`.
-/
theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  simp [blk, symm_castSucc, symm_last]

/- English proof (translation)
Simplify using `[blk, symm_castSucc, symm_last]`.
-/
theorem blk_lc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk A b a e (Fin.last n) j.castSucc = a j := by
  simp [blk, symm_castSucc, symm_last]

/- English proof (translation)
Simplify using `[blk, symm_last]`.
-/
theorem blk_ll {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    blk A b a e (Fin.last n) (Fin.last n) = e := by
  simp [blk, symm_last]

/- English proof (translation)
Unfold `blk`. Rewrite using `[Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`. Use `congr 2`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.vecMulVec_apply]`.

Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.vecMul, dotProduct]`. Use extensionality with `i j`.

Simplify using `[Matrix.mul_apply, dotProduct]`.
-/
theorem blk_mul {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b a b' a' : Fin n → ℂ) (e e' : ℂ) :
    blk A b a e * blk A' b' a' e' =
      blk (A * A' + Matrix.vecMulVec b a') (A *ᵥ b' + e' • b) (a ᵥ* A' + e • a') (a ⬝ᵥ b' + e * e') := by
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  congr 2
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply, dotProduct]

/- English proof (translation)
Unfold `blk`. Rewrite using `[Matrix.det_reindex_self]`. Establish `h : (Matrix.of fun i (_ : Fin 1) => (0 : Fin n → ℂ) i) = (0 : Matrix (Fin n) (Fin 1) ℂ)`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite using `[h, Matrix.det_fromBlocks_zero₁₂]`. Simplify using the standard rewrite rules.
-/
theorem det_blk_col_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ) (e : ℂ) :
    (blk A 0 a e).det = A.det * e := by
  unfold blk
  rw [Matrix.det_reindex_self]
  have h : (Matrix.of fun i (_ : Fin 1) => (0 : Fin n → ℂ) i) = (0 : Matrix (Fin n) (Fin 1) ℂ) := by
    ext i j; simp
  rw [h, Matrix.det_fromBlocks_zero₁₂]
  simp

/- English proof (translation)
Unfold `blk`. Rewrite using `[Matrix.det_reindex_self]`. Establish `h : (Matrix.of fun (_ : Fin 1) j => (0 : Fin n → ℂ) j) = (0 : Matrix (Fin 1) (Fin n) ℂ)`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite using `[h, Matrix.det_fromBlocks_zero₂₁]`. Simplify using the standard rewrite rules.
-/
theorem det_blk_row_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (e : ℂ) :
    (blk A b 0 e).det = A.det * e := by
  unfold blk
  rw [Matrix.det_reindex_self]
  have h : (Matrix.of fun (_ : Fin 1) j => (0 : Fin n → ℂ) j) = (0 : Matrix (Fin 1) (Fin n) ℂ) := by
    ext i j; simp
  rw [h, Matrix.det_fromBlocks_zero₂₁]
  simp

/- English proof (translation)
Establish `h : (upper v).BlockTriangular id`. Introduce `i j hij`. Establish `hij' : j < i` using `hij`. Simplify using `[upper, strictUpper, Matrix.one_apply, hij'.ne', not_lt.2 hij'.le]`. Rewrite using `[Matrix.det_of_isUpperTriangular h]`.

Simplify using `[upper, strictUpper]`.
-/
theorem det_upper {d : ℕ} (v : UT d → ℂ) : (upper v).det = 1 := by
  have h : (upper v).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    simp [upper, strictUpper, Matrix.one_apply, hij'.ne', not_lt.2 hij'.le]
  rw [Matrix.det_of_isUpperTriangular h]
  simp [upper, strictUpper]

/- English proof (translation)
Simplify using `[wMat, Matrix.mul_apply]`.
-/
theorem wMat_mul_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (wMat n * A) i j = A i.rev j := by
  simp [wMat, Matrix.mul_apply]

/- English proof (translation)
Simplify using `[wMat, Matrix.mulVec, dotProduct]`.
-/
theorem wMat_mulVec_apply {n : ℕ} (B : Fin n → ℂ) (i : Fin n) : (wMat n *ᵥ B) i = B i.rev := by
  simp [wMat, Matrix.mulVec, dotProduct]

/- English proof (translation)
Rewrite using `[Matrix.det_succ_row_zero]`. Rewrite using `[Finset.sum_eq_single (Fin.last n)]`. Establish `h : (wMat (n + 1)).submatrix Fin.succ (Fin.last n).succAbove = wMat n`. Use extensionality with `i j`. Simplify using `[wMat, Fin.rev_succ]`.

Rewrite using `[h]`. Simplify using `[wMat]`. Introduce `j _ hj`. Simplify using `[wMat, hj]`. Simplify using the standard rewrite rules.
-/
theorem det_wMat_succ (n : ℕ) : (wMat (n + 1)).det = (-1) ^ n * (wMat n).det := by
  rw [Matrix.det_succ_row_zero]
  rw [Finset.sum_eq_single (Fin.last n)]
  · have h : (wMat (n + 1)).submatrix Fin.succ (Fin.last n).succAbove = wMat n := by
      ext i j
      simp [wMat, Fin.rev_succ]
    rw [h]
    simp [wMat]
  · intro j _ hj
    simp [wMat, hj]
  · simp

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[det_wMat_succ]`. Conclude with `mul_ne_zero (pow_ne_zero _ (by norm_num)) ih`.
-/
theorem det_wMat_ne_zero (n : ℕ) : (wMat n).det ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [det_wMat_succ]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) ih

end Formalism.FourierDecayAlt.P.G2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2

/- English proof (translation)
Introduce `β x y`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[psi, mul_add, Complex.exp_add]`. Simplify using `only [psi]`. Rewrite using `[mul_comm]`.

Conclude with `Complex.norm_exp_ofReal_mul_I _`. Simplify using `[psi]`.
-/
theorem additive_character_psi : Formalism.FourierDecayAlt.G.PsiChar := by
  intro β x y
  refine ⟨?_, ?_, ?_⟩
  · simp [psi, mul_add, Complex.exp_add]
  · simp only [psi]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  · simp [psi]

/- English proof (translation)
Introduce `n p q`. Establish `key : ∀ p q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsUpperUni p → IsUpperUni q → superSum (p * q) = superSum p + superSum q`. Introduce `p q hp hq`. Simplify using `only [superSum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply]`. Establish `hne : i.castSucc ≠ i.succ` using `(Fin.castSucc_lt_succ).ne`. Rewrite using `[Finset.sum_eq_add i.castSucc i.succ hne]`. Rewrite using `[hp.1, hq.1]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `k _ hk`. Break down `lt_trichotomy k i.castSucc with h | h | h` into its components or cases. Rewrite using `[hp.2 _ _ h]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `absurd h hk.1`.

Establish `: i.succ < k`. Break down `lt_or_eq_of_le (Fin.castSucc_lt_iff_succ_le.1 h) with h' | h'` into its components or cases. Conclude with `h'`. Conclude with `absurd h'.symm hk.2`. Rewrite using `[hq.2 _ _ this]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Use `⟨key p q, fun hp hq => ?_⟩` and prove the remaining obligations. Use `key qᵀ pᵀ hq hp` as an intermediate fact.

Establish `e : ∀ l : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, subSum l = superSum lᵀ` using `fun l => rfl`. Rewrite using `[e, e, e, Matrix.transpose_mul, this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem character_additive : Formalism.FourierDecayAlt.G.CharAdditive := by
  intro n p q
  have key : ∀ p q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsUpperUni p → IsUpperUni q →
      superSum (p * q) = superSum p + superSum q := by
    intro p q hp hq
    simp only [superSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_apply]
    have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ).ne
    rw [Finset.sum_eq_add i.castSucc i.succ hne]
    · rw [hp.1, hq.1]; ring
    · intro k _ hk
      rcases lt_trichotomy k i.castSucc with h | h | h
      · rw [hp.2 _ _ h]; ring
      · exact absurd h hk.1
      · have : i.succ < k := by
          rcases lt_or_eq_of_le (Fin.castSucc_lt_iff_succ_le.1 h) with h' | h'
          · exact h'
          · exact absurd h'.symm hk.2
        rw [hq.2 _ _ this]; ring
    · simp
    · simp
  refine ⟨key p q, fun hp hq => ?_⟩
  have := key qᵀ pᵀ hq hp
  have e : ∀ l : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, subSum l = superSum lᵀ := fun l => rfl
  rw [e, e, e, Matrix.transpose_mul, this]; ring

/- English proof (translation)
Introduce `n` and use `⟨det_wMat_succ n, det_wMat_ne_zero n⟩`.
-/
theorem det_weyl_matrix : Formalism.FourierDecayAlt.G.DetMatch :=
  fun n => ⟨det_wMat_succ n, det_wMat_ne_zero n⟩

/- English proof (translation)
Use `⟨fun n t c p => ?_, fun d z v => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, Matrix.det_mul, lowRow, ptBlock, det_blk_col_zero, det_blk_col_zero, det_blk_row_zero, det_upper, Matrix.det_smul] simp`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Matrix.det_mul, det_upper, ptLong, Matrix.det_smul] simp`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_orbit : Formalism.FourierDecayAlt.G.DetOrbit := by
  refine ⟨fun n t c p => ?_, fun d z v => ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, lowRow, ptBlock, det_blk_col_zero, det_blk_col_zero,
      det_blk_row_zero, det_upper, Matrix.det_smul]
    simp; ring
  · rw [Matrix.det_mul, det_upper, ptLong, Matrix.det_smul]
    simp; ring

/- English proof (translation)
Introduce `n t c p`. Take `⟨a, v, b⟩` from `p`. Simplify using `only [lowRow, ptBlock, Mcoord, blk_mul, Xof, rhoOf, upper]`. Use `congr 1`. Simplify using `[Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, smul_add]`.

Use extensionality with `i`. Simplify using `[Matrix.mulVec_smul, Matrix.smul_mulVec]`. Simplify using `[Matrix.vecMul_smul, Matrix.mul_add, Matrix.vecMul_add, smul_add, Matrix.smul_vecMul, ← Matrix.vecMul_vecMul]`. Simplify using `[Matrix.mulVec_smul, Matrix.vecMul_smul, Matrix.dotProduct_mulVec, add_comm]`.
-/
theorem matrix_entries : Formalism.FourierDecayAlt.G.EntriesM := by
  intro n t c p
  obtain ⟨a, v, b⟩ := p
  simp only [lowRow, ptBlock, Mcoord, blk_mul, Xof, rhoOf, upper]
  congr 1
  · simp [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, smul_add]
  · ext i; simp [Matrix.mulVec_smul, Matrix.smul_mulVec]
  · simp [Matrix.vecMul_smul, Matrix.mul_add, Matrix.vecMul_add, smul_add, Matrix.smul_vecMul,
      ← Matrix.vecMul_vecMul]
  · simp [Matrix.mulVec_smul, Matrix.vecMul_smul, Matrix.dotProduct_mulVec, add_comm]

/- English proof (translation)
Introduce `m t σ X B ρ hX`. Use `⟨fun i j hij => ?_, fun i j hij => ?_, fun k => ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨i', rfl⟩ : ∃ i' : Fin (m + 1), i = i'.castSucc` from `⟨⟨i, by omega⟩, Fin.ext rfl⟩`. Take `⟨j', rfl⟩ : ∃ j' : Fin (m + 1), j = j'.castSucc` from `⟨⟨j, by omega⟩, Fin.ext rfl⟩`. Establish `hlt : j' < i'.rev`.

Rewrite using `[Fin.lt_def, Fin.val_rev]`. Simplify using `only [Fin.val_castSucc] at hij`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Mcoord, blk_cc, wMat_mul_apply]`. Simplify using `[Matrix.one_apply, hlt.ne', hX _ _ hlt.le]`.

Take `⟨i', rfl⟩ : ∃ i' : Fin (m + 1), i = i'.castSucc` from `⟨⟨i, by omega⟩, Fin.ext rfl⟩`. Take `⟨j', rfl⟩ : ∃ j' : Fin (m + 1), j = j'.castSucc` from `⟨⟨j, by omega⟩, Fin.ext rfl⟩`. Establish `heq : i'.rev = j'`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[Fin.val_rev]`.

Simplify using `only [Fin.val_castSucc] at hij`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Mcoord, blk_cc, wMat_mul_apply, heq]`. Simplify using `[hX _ _ le_rfl]`. Rewrite using `[Mcoord, xOf]`.

Use `Fin.lastCases ?_ (fun k' => ?_) k` and prove the remaining obligations. Rewrite using `[Fin.succ_last, blk_cl, blk_cl, wMat_mulVec_apply, Fin.rev_rev]`. Rewrite using `[Fin.succ_castSucc, blk_cc, blk_cc, wMat_mul_apply, Fin.rev_rev]`. Establish `hne : k'.castSucc ≠ k'.succ` using `(Fin.castSucc_lt_succ).ne`. Simplify using `[Matrix.one_apply, hne]`.

Establish `h0 : (0 : Fin (m + 1 + 1)) = (0 : Fin (m + 1)).castSucc` using `rfl`. Rewrite using `[Mcoord, h0, blk_lc]`. Rewrite using `[Mcoord, blk_ll]`.
-/
theorem shape_of_matrix : Formalism.FourierDecayAlt.G.ShapeM := by
  intro m t σ X B ρ hX
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun k => ?_, ?_, ?_⟩
  · obtain ⟨i', rfl⟩ : ∃ i' : Fin (m + 1), i = i'.castSucc :=
      ⟨⟨i, by omega⟩, Fin.ext rfl⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin (m + 1), j = j'.castSucc :=
      ⟨⟨j, by omega⟩, Fin.ext rfl⟩
    have hlt : j' < i'.rev := by
      rw [Fin.lt_def, Fin.val_rev]
      simp only [Fin.val_castSucc] at hij
      omega
    rw [Mcoord, blk_cc, wMat_mul_apply]
    simp [Matrix.one_apply, hlt.ne', hX _ _ hlt.le]
  · obtain ⟨i', rfl⟩ : ∃ i' : Fin (m + 1), i = i'.castSucc :=
      ⟨⟨i, by omega⟩, Fin.ext rfl⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin (m + 1), j = j'.castSucc :=
      ⟨⟨j, by omega⟩, Fin.ext rfl⟩
    have heq : i'.rev = j' := by
      apply Fin.ext
      rw [Fin.val_rev]
      simp only [Fin.val_castSucc] at hij
      omega
    rw [Mcoord, blk_cc, wMat_mul_apply, heq]
    simp [hX _ _ le_rfl]
  · rw [Mcoord, xOf]
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · rw [Fin.succ_last, blk_cl, blk_cl, wMat_mulVec_apply, Fin.rev_rev]
    · rw [Fin.succ_castSucc, blk_cc, blk_cc, wMat_mul_apply, Fin.rev_rev]
      have hne : k'.castSucc ≠ k'.succ := (Fin.castSucc_lt_succ).ne
      simp [Matrix.one_apply, hne]
  · have h0 : (0 : Fin (m + 1 + 1)) = (0 : Fin (m + 1)).castSucc := rfl
    rw [Mcoord, h0, blk_lc]
  · rw [Mcoord, blk_ll]

/- English proof (translation)
Introduce `m t ht p`. Take `⟨a, v, b⟩` from `p`. Establish `h1 : subSum (lowRow a) = a (Fin.last m)`. Rewrite using `[subSum, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add, Fin.succ_last, lowRow, blk_lc]`. Introduce `i _`.

Establish `hne : i.succ ≠ i.castSucc` using `(Fin.castSucc_lt_succ).ne'`. Rewrite using `[Fin.succ_castSucc, lowRow, blk_cc, Matrix.one_apply_ne hne]`. Establish `h2 : rhoOf t a v 0 = t * a (Fin.last m)`. Simplify using `only [rhoOf, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, wMat_mul_apply]`. Use `congr 1`.

Rewrite using `[Finset.sum_eq_single (Fin.last m)]`. Simplify using `[upper, strictUpper]`. Introduce `i _ hi`. Establish `hne : i.rev ≠ 0`. Introduce `h`.

Apply `hi` to reduce the goal to its premises. Rewrite using `[← Fin.rev_rev i, h, Fin.rev_zero]`. Establish `hnl : ¬ i.rev < 0` using `by simp`. Simplify using `[upper, strictUpper, Matrix.one_apply_ne hne]`. Simplify using the standard rewrite rules.

Establish `h3 : ∀ k : Fin (m + 1), xOf (Xof t v) (t • b) k = t * blk (upper v) b 0 1 k.castSucc k.succ`. Introduce `k`. Rewrite using `[xOf]`. Use `Fin.lastCases ?_ (fun k' => ?_) k` and prove the remaining obligations. Rewrite using `[Fin.succ_last, blk_cl, blk_cl]`.

Simplify using the standard rewrite rules. Rewrite using `[Fin.succ_castSucc, blk_cc, blk_cc]`. Establish `hne : k'.castSucc ≠ k'.succ` using `(Fin.castSucc_lt_succ).ne`. Simplify using `[Xof, upper, Matrix.one_apply_ne hne]`. Use `show subSum (lowRow a) + superSum (blk (upper v) b 0 1) = (rhoOf t a v 0 + ∑ k, xOf (Xof t v) (t • b) k) / t`.

Rewrite using `[h1, h2, superSum, Finset.sum_congr rfl (fun k _ => h3 k), ← Finset.mul_sum]`. Clear the denominators using the available nonvanishing facts.
-/
theorem phase_formula : Formalism.FourierDecayAlt.G.PhaseFormula := by
  intro m t ht p
  obtain ⟨a, v, b⟩ := p
  have h1 : subSum (lowRow a) = a (Fin.last m) := by
    rw [subSum, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add, Fin.succ_last, lowRow, blk_lc]
    intro i _
    have hne : i.succ ≠ i.castSucc := (Fin.castSucc_lt_succ).ne'
    rw [Fin.succ_castSucc, lowRow, blk_cc, Matrix.one_apply_ne hne]
  have h2 : rhoOf t a v 0 = t * a (Fin.last m) := by
    simp only [rhoOf, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, wMat_mul_apply]
    congr 1
    rw [Finset.sum_eq_single (Fin.last m)]
    · simp [upper, strictUpper]
    · intro i _ hi
      have hne : i.rev ≠ 0 := by
        intro h
        apply hi
        rw [← Fin.rev_rev i, h, Fin.rev_zero]
      have hnl : ¬ i.rev < 0 := by simp
      simp [upper, strictUpper, Matrix.one_apply_ne hne]
    · simp
  have h3 : ∀ k : Fin (m + 1), xOf (Xof t v) (t • b) k = t * blk (upper v) b 0 1 k.castSucc k.succ := by
    intro k
    rw [xOf]
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · rw [Fin.succ_last, blk_cl, blk_cl]; simp
    · rw [Fin.succ_castSucc, blk_cc, blk_cc]
      have hne : k'.castSucc ≠ k'.succ := (Fin.castSucc_lt_succ).ne
      simp [Xof, upper, Matrix.one_apply_ne hne]
  show subSum (lowRow a) + superSum (blk (upper v) b 0 1) =
    (rhoOf t a v 0 + ∑ k, xOf (Xof t v) (t • b) k) / t
  rw [h1, h2, superSum, Finset.sum_congr rfl (fun k _ => h3 k), ← Finset.mul_sum]
  field_simp

end Formalism.FourierDecayAlt.P
