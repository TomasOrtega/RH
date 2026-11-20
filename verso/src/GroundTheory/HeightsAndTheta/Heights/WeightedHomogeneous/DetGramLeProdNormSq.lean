import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace HadamardGramBound

/- English proof (translation)
Use `set K := Submodule.span ℝ (Set.range w)`. Establish `hK : Module.finrank ℝ K = Fintype.card (Fin n)` using `finrank_span_eq_card hw`. Establish `: FiniteDimensional ℝ K` using `FiniteDimensional.span_of_finite ℝ (Set.finite_range w)`. Set `w' : Fin n → K` to `fun i => ⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩`. Establish `hg : Matrix.gram ℝ w = Matrix.gram ℝ w'`.

Use extensionality with `i j`. Simplify using `[Matrix.gram_apply, w']`. Set `gb` to `InnerProductSpace.gramSchmidtOrthonormalBasis hK w'`. Establish `hdet : gb.toBasis.det w' = ∏ i, inner ℝ (gb i) (w' i)` using `InnerProductSpace.gramSchmidtOrthonormalBasis_det hK w'`. Rewrite using `[hg, Matrix.gram_eq_conjTranspose_mul gb, Matrix.det_mul, Matrix.det_conjTranspose]`.

Establish `hM : (Matrix.of fun i j => gb.repr (w' j) i) = gb.toBasis.toMatrix w'`. Use extensionality with `i j`. Simplify using `[Module.Basis.toMatrix_apply]`. Rewrite using `[hM, ← Module.Basis.det_apply, hdet, star_trivial, ← sq, ← Finset.prod_pow]`. Use `Finset.prod_le_prod (fun i _ => sq_nonneg _) (fun i _ => ?_)` and prove the remaining obligations.

Establish `h1` using `abs_real_inner_le_norm (gb i) (w' i)`. Rewrite `h1` using `[gb.orthonormal.1 i, one_mul]`. Establish `h2 : ‖w' i‖ = ‖w i‖` using `rfl`. Rewrite using `[← h2, ← sq_abs]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) h1 2`.
-/
theorem det_gram_le_prod_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (w : Fin n → V) (hw : LinearIndependent ℝ w) :
    (Matrix.gram ℝ w).det ≤ ∏ i, ‖w i‖ ^ 2 := by
  set K := Submodule.span ℝ (Set.range w)
  have hK : Module.finrank ℝ K = Fintype.card (Fin n) := finrank_span_eq_card hw
  have : FiniteDimensional ℝ K := FiniteDimensional.span_of_finite ℝ (Set.finite_range w)
  let w' : Fin n → K := fun i => ⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hg : Matrix.gram ℝ w = Matrix.gram ℝ w' := by
    ext i j
    simp [Matrix.gram_apply, w']
  let gb := InnerProductSpace.gramSchmidtOrthonormalBasis hK w'
  have hdet : gb.toBasis.det w' = ∏ i, inner ℝ (gb i) (w' i) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det hK w'
  rw [hg, Matrix.gram_eq_conjTranspose_mul gb, Matrix.det_mul, Matrix.det_conjTranspose]
  have hM : (Matrix.of fun i j => gb.repr (w' j) i) = gb.toBasis.toMatrix w' := by
    ext i j
    simp [Module.Basis.toMatrix_apply]
  rw [hM, ← Module.Basis.det_apply, hdet, star_trivial, ← sq, ← Finset.prod_pow]
  refine Finset.prod_le_prod (fun i _ => sq_nonneg _) (fun i _ => ?_)
  have h1 := abs_real_inner_le_norm (gb i) (w' i)
  rw [gb.orthonormal.1 i, one_mul] at h1
  have h2 : ‖w' i‖ = ‖w i‖ := rfl
  rw [← h2, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem gram_comb {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → V) :
    Matrix.gram ℝ (fun i => ∑ j, M i j • b j) = M * Matrix.gram ℝ b * M.transpose := by
  ext i k
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Introduce `V _ _ r v b hv hn hb`. Use `choose M hM using fun i => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hb i)`. Use `set N : Matrix (Fin r) (Fin r) ℝ := (Matrix.of M).map (Int.cast : ℤ → ℝ) with hNdef`. Establish `hvN : v = fun i => ∑ j, N i j • b j`. Use function extensionality and compare the values at `i`.

Rewrite using `[← hM i]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[N, Int.cast_smul_eq_zsmul]`. Establish `hG : Matrix.gram ℝ v = N * Matrix.gram ℝ b * N.transpose`. Rewrite using `[hvN]`.

Conclude with `gram_comb N b`. Establish `hdet : (Matrix.gram ℝ v).det = N.det ^ 2 * (Matrix.gram ℝ b).det`. Rewrite using `[hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]`. Expand and normalize the polynomial expressions, which then agree. Establish `hvpos : 0 < (Matrix.gram ℝ v).det` using `(Matrix.posDef_gram_of_linearIndependent hv).det_pos`.

Establish `hbnn : 0 ≤ (Matrix.gram ℝ b).det` using `(Matrix.posSemidef_gram ℝ b).det_nonneg`. Establish `hNdet : N.det = (((Matrix.of M).det : ℤ) : ℝ)`. Rewrite using `[hNdef]`. Conclude with `((Int.castRingHom ℝ).map_det (Matrix.of M)).symm`. Establish `hN0 : N.det ≠ 0`.

Introduce `h`. Rewrite `hvpos` using `[hdet, h]`. Simplify using `at hvpos`. Establish `hN1 : 1 ≤ N.det ^ 2`. Rewrite `hN0`, the goal using `[hNdet]`.

Establish `hd : (Matrix.of M).det ≠ 0` using `by exact_mod_cast hN0`. Establish `: (1 : ℤ) ≤ (Matrix.of M).det ^ 2`. Apply the tactic sequence `rcases lt_or_gt_of_ne hd with h | h <;> nlinarith`. Conclude with `this` after adjusting the coercions. Establish `hHad` using `det_gram_le_prod_norm_sq v hv`.

Establish `hprod : ∏ i, ‖v i‖ ^ 2 ≤ 1` using `Finset.prod_le_one (fun i _ => sq_nonneg _) fun i _ => pow_le_one₀ (norm_nonneg _) (hn i)`. Express the relevant statement in the definitionally equal form `0 < (Matrix.gram ℝ b).det ∧ (Matrix.gram ℝ b).det ≤ 1`. Use `⟨lt_of_le_of_ne hbnn fun h => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hvpos` using `[hdet, ← h]`. Simplify using `at hvpos`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem proof : HadamardGramBound.Statement := by
  intro V _ _ r v b hv hn hb
  choose M hM using fun i => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hb i)
  set N : Matrix (Fin r) (Fin r) ℝ := (Matrix.of M).map (Int.cast : ℤ → ℝ) with hNdef
  have hvN : v = fun i => ∑ j, N i j • b j := by
    funext i
    rw [← hM i]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [N, Int.cast_smul_eq_zsmul]
  have hG : Matrix.gram ℝ v = N * Matrix.gram ℝ b * N.transpose := by
    rw [hvN]
    exact gram_comb N b
  have hdet : (Matrix.gram ℝ v).det = N.det ^ 2 * (Matrix.gram ℝ b).det := by
    rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hvpos : 0 < (Matrix.gram ℝ v).det := (Matrix.posDef_gram_of_linearIndependent hv).det_pos
  have hbnn : 0 ≤ (Matrix.gram ℝ b).det := (Matrix.posSemidef_gram ℝ b).det_nonneg
  have hNdet : N.det = (((Matrix.of M).det : ℤ) : ℝ) := by
    rw [hNdef]
    exact ((Int.castRingHom ℝ).map_det (Matrix.of M)).symm
  have hN0 : N.det ≠ 0 := by
    intro h
    rw [hdet, h] at hvpos
    simp at hvpos
  have hN1 : 1 ≤ N.det ^ 2 := by
    rw [hNdet] at hN0 ⊢
    have hd : (Matrix.of M).det ≠ 0 := by exact_mod_cast hN0
    have : (1 : ℤ) ≤ (Matrix.of M).det ^ 2 := by
      rcases lt_or_gt_of_ne hd with h | h <;> nlinarith
    exact_mod_cast this
  have hHad := det_gram_le_prod_norm_sq v hv
  have hprod : ∏ i, ‖v i‖ ^ 2 ≤ 1 :=
    Finset.prod_le_one (fun i _ => sq_nonneg _) fun i _ => pow_le_one₀ (norm_nonneg _) (hn i)
  change 0 < (Matrix.gram ℝ b).det ∧ (Matrix.gram ℝ b).det ≤ 1
  refine ⟨lt_of_le_of_ne hbnn fun h => ?_, ?_⟩
  · rw [hdet, ← h] at hvpos
    simp at hvpos
  · nlinarith

end HadamardGramBound

end GroundTheory.Heights₂.Heights
