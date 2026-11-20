import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder

namespace GlobalTheory.FramePotential

/- English proof (translation)
Use `set A : Matrix (Fin p) (Fin p) ℂ := g.submatrix (Fin.castLE h) (Fin.castLE h) with hA`. Use `set C : Matrix (Fin n) (Fin p) ℂ := Matrix.of fun k a => if (k : ℕ) < p then 0 else g k (Fin.castLE h a) with hC`. Establish `key : Aᴴ * A = 1 + Cᴴ * C`. Use extensionality with `a b`. Establish `e` using `congrFun (congrFun hg (Fin.castLE h b)) (Fin.castLE h a)`.

Rewrite `e` using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply, Fin.castLE_inj] at e`. Establish `e1 : (1 : Matrix (Fin p) (Fin p) ℂ) a b = ∑ k, g k (Fin.castLE h b) * ((sgn p (k : ℕ) : ℝ) : ℂ) * starRingEnd ℂ (g k (Fin.castLE h a))`. Rewrite using `[e, Matrix.one_apply]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using `[sgn]`. Rewrite using `[if_neg hab, if_neg (Ne.symm hab)]`. Establish `e2 : (Aᴴ * A) a b = ∑ k : Fin n, if (k : ℕ) < p then starRingEnd ℂ (g k (Fin.castLE h a)) * g k (Fin.castLE h b) else 0`. Rewrite using `[Matrix.mul_apply]`.

Use `Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun k hk => ?_) (fun k => ?_)` and prove the remaining obligations. Rewrite using `[if_neg]`. Introduce `hlt`. Conclude with `hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩`. Simplify using `[hA, Matrix.conjTranspose_apply]`.

Rewrite using `[e2, Matrix.add_apply, e1, Matrix.mul_apply, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : (k : ℕ) < p`. Simplify using `[hC, sgn, hk, Matrix.conjTranspose_apply, mul_comm]`. Simplify using `[hC, sgn, hk, Matrix.conjTranspose_apply, mul_comm]`.

Establish `h1` using `sumBd_det_one_add_ge (Matrix.posSemidef_conjTranspose_mul_self C)`. Rewrite `h1` using `[← key, sumBd_normSq_det, sumBd_trace_ctm]`. Establish `h2` using `sumBdFsq_nonneg C`. Rewrite using `[← Complex.normSq_eq_norm_sq]`. Use `show 1 ≤ Complex.normSq A.det`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_norm_lminor_sq {n p : ℕ} (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : gᵀ * (Matrix.diagonal fun a : Fin n => ((sgn p (a : ℕ) : ℝ) : ℂ)) * g.map (starRingEnd ℂ) =
      Matrix.diagonal fun a : Fin n => ((sgn p (a : ℕ) : ℝ) : ℂ)) :
    1 ≤ ‖lminor g ⟨p, Nat.lt_succ_of_le h⟩‖ ^ 2 := by
  set A : Matrix (Fin p) (Fin p) ℂ := g.submatrix (Fin.castLE h) (Fin.castLE h) with hA
  set C : Matrix (Fin n) (Fin p) ℂ :=
    Matrix.of fun k a => if (k : ℕ) < p then 0 else g k (Fin.castLE h a) with hC
  have key : Aᴴ * A = 1 + Cᴴ * C := by
    ext a b
    have e := congrFun (congrFun hg (Fin.castLE h b)) (Fin.castLE h a)
    rw [Matrix.mul_apply] at e
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.diagonal_apply, Fin.castLE_inj] at e
    have e1 : (1 : Matrix (Fin p) (Fin p) ℂ) a b =
        ∑ k, g k (Fin.castLE h b) * ((sgn p (k : ℕ) : ℝ) : ℂ) * starRingEnd ℂ (g k (Fin.castLE h a)) := by
      rw [e, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp [sgn]
      · rw [if_neg hab, if_neg (Ne.symm hab)]
    have e2 : (Aᴴ * A) a b = ∑ k : Fin n, if (k : ℕ) < p then
        starRingEnd ℂ (g k (Fin.castLE h a)) * g k (Fin.castLE h b) else 0 := by
      rw [Matrix.mul_apply]
      refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun k hk => ?_)
        (fun k => ?_)
      · rw [if_neg]
        intro hlt
        exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
      · simp [hA, Matrix.conjTranspose_apply]
    rw [e2, Matrix.add_apply, e1, Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < p
    · simp [hC, sgn, hk, Matrix.conjTranspose_apply, mul_comm]
    · simp [hC, sgn, hk, Matrix.conjTranspose_apply, mul_comm]
  have h1 := sumBd_det_one_add_ge (Matrix.posSemidef_conjTranspose_mul_self C)
  rw [← key, sumBd_normSq_det, sumBd_trace_ctm] at h1
  have h2 := sumBdFsq_nonneg C
  rw [← Complex.normSq_eq_norm_sq]
  show 1 ≤ Complex.normSq A.det
  linarith

/- English proof (translation)
Establish `h` using `Nat.le_of_lt_succ k.isLt`. Unfold `lminor`. Rewrite using `[FrameDegreeData.sub_mul_sub h M B (fun a c m hm => by`. Rewrite using `[FrameDegreeData.upper_lt hB (show Fin.castLE h c < m by rw [Fin.lt_def]; simp; omega), mul_zero]),`. Use the proof step `Matrix.det_mul, FrameDegreeData.det_sub_upper h hB]`.
-/
theorem lminor_mul_upper {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.BlockTriangular id) (k : Fin (n + 1)) :
    lminor (M * B) k = lminor M k * ∏ j : Fin k, B (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) := by
  have h := Nat.le_of_lt_succ k.isLt
  unfold lminor
  rw [FrameDegreeData.sub_mul_sub h M B (fun a c m hm => by
      rw [FrameDegreeData.upper_lt hB (show Fin.castLE h c < m by rw [Fin.lt_def]; simp; omega), mul_zero]),
    Matrix.det_mul, FrameDegreeData.det_sub_upper h hB]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `e : mat (rmul x b) τ = mat x τ * mat b τ` using `rfl`. Rewrite using `[FrameDegreeData.dmin_rmul X x hb, e, ← Matrix.mul_assoc, lminor_mul_upper _ (FrameDegreeData.upper_of_bor X hb τ)]`. Establish `hc : (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => FrameDegreeData.bdiag_ne X hb τ _`. Generalize the expression as in `(∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) = c at hc ⊢`. Establish `hc' : ‖c‖ ^ 2 ≠ 0` using `pow_ne_zero _ (norm_ne_zero_iff.mpr hc)`.

Rewrite using `[norm_mul, norm_mul, norm_mul, Complex.norm_conj, mul_pow, ← mul_div_mul_right ‖dmin X.Gm x τ i‖ _ hc']`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem factor_rmul {r : ℕ} (X : Data E r) (x0 x : Frame X.Ψ r) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm (rmul x b) τ i‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (rmul x b) τ) i‖ ^ 2 =
      ‖dmin X.Gm x τ i‖ / ‖lminor ((mat x0 τ)⁻¹ * mat x τ) i‖ ^ 2 := by
  have e : mat (rmul x b) τ = mat x τ * mat b τ := rfl
  rw [FrameDegreeData.dmin_rmul X x hb, e, ← Matrix.mul_assoc,
    lminor_mul_upper _ (FrameDegreeData.upper_of_bor X hb τ)]
  have hc : (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => FrameDegreeData.bdiag_ne X hb τ _
  generalize (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) = c at hc ⊢
  have hc' : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hc)
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, mul_pow,
    ← mul_div_mul_right ‖dmin X.Gm x τ i‖ _ hc']
  congr 1
  ring

/- English proof (translation)
Unfold `dmin lminor`. Rewrite using `[hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, sgn]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem norm_dmin_of_isOrth {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ)
    (i : Fin (r + 1)) : ‖dmin X.Gm x τ i‖ = 1 := by
  unfold dmin lminor
  rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _),
    Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp, sgn]
  split_ifs <;> simp

/- English proof (translation)
Apply `one_le_norm_lminor_sq X.p0_le` to reduce the goal to its premises. Establish `hu : IsUnit (mat x0 τ).det` using `isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)`. Use `conv_lhs => rw [← h0 τ]`. Rewrite using `[← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv_cancel_left _ _ hu, hx τ]`.
-/
theorem one_le_minor_of_isOrth {r : ℕ} (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : IsOrth X x) (τ : X.Ψ) :
    1 ≤ ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 := by
  apply one_le_norm_lminor_sq X.p0_le
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)
  conv_lhs => rw [← h0 τ]
  rw [← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv_cancel_left _ _ hu, hx τ]

/- English proof (translation)
Take `⟨x1, h1, b, hb, rfl⟩` from `ortho_holds r X x hx`. Rewrite using `[factor_rmul X x0 x1 hb, norm_dmin_of_isOrth X h1]`. Establish `h` using `one_le_minor_of_isOrth X h0 h1 τ`. Conclude with `⟨div_pos one_pos (by linarith), (div_le_one (by linarith)).mpr h⟩`.
-/
theorem factor_mem {r : ℕ} (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : x ∈ X.dom) (τ : X.Ψ) :
    0 < ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ /
        ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 ∧
      ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ /
        ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 ≤ 1 := by
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X x hx
  rw [factor_rmul X x0 x1 hb, norm_dmin_of_isOrth X h1]
  have h := one_le_minor_of_isOrth X h0 h1 τ
  exact ⟨div_pos one_pos (by linarith), (div_le_one (by linarith)).mpr h⟩

/- English proof (translation)
Establish `hu : IsUnit (mat x0 τ).det` using `isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)`. Establish `e : mat (cpt X x0 z) τ = mat x0 τ * mat (nmat X z) τ` using `rfl`. Rewrite using `[e, Matrix.nonsing_inv_mul_cancel_left _ _ hu, ← Matrix.mul_one (mat (nmat X z) τ), LUPf.lminor_nb _ _ (fun a c hac => ?_) (fun a => ?_) Matrix.blockTriangular_one]`. Simplify using the standard rewrite rules. Simplify using `[mat, nmat, hac.ne, not_lt.mpr hac.le]`.

Simplify using `[mat, nmat]`.
-/
theorem lminor_cpt {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (h0 : IsOrth X x0) (z : V (nd X))
    (τ : X.Ψ) (i : Fin (r + 1)) : lminor ((mat x0 τ)⁻¹ * mat (cpt X x0 z) τ) i = 1 := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)
  have e : mat (cpt X x0 z) τ = mat x0 τ * mat (nmat X z) τ := rfl
  rw [e, Matrix.nonsing_inv_mul_cancel_left _ _ hu, ← Matrix.mul_one (mat (nmat X z) τ),
    LUPf.lminor_nb _ _ (fun a c hac => ?_) (fun a => ?_) Matrix.blockTriangular_one]
  · simp
  · simp [mat, nmat, hac.ne, not_lt.mpr hac.le]
  · simp [mat, nmat]

/- English proof (translation)
Introduce `r X x0 h0`. Use `⟨?_, fun x hx => ⟨?_, ?_⟩, fun x _ b hb => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Use `Finset.measurable_prod _ fun τ _ => Measurable.div ?_ ?_` and prove the remaining obligations. Conclude with `(ExtFPf.cont_dmin X τ _).norm.measurable`. Establish `hm : Continuous fun x : Frame X.Ψ r => mat x τ` using `continuous_apply τ`.

Conclude with `((((continuous_const.matrix_mul hm).matrix_submatrix _ _).matrix_det).norm.pow 2).measurable`. Conclude with `Finset.prod_pos fun τ _ => (factor_mem X h0 hx τ).1`. Conclude with `Finset.prod_le_one (fun τ _ => (factor_mem X h0 hx τ).1.le) fun τ _ => (factor_mem X h0 hx τ).2`. Conclude with `Finset.prod_congr rfl fun τ _ => factor_rmul X x0 x hb τ _`. Unfold `rhF`.

Rewrite using `[neg_neg, Real.exp_sum]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[lminor_cpt X h0, Real.exp_log (norm_pos_iff.mpr (FlowCoefficientBounds.dmin_ne X hz τ _))]`. Simplify using the standard rewrite rules.
-/
theorem frame_potential_basic :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → Measurable (fun x : Frame X.Ψ r => (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) ∧ (∀ x ∈ X.dom, 0 < (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ∧ (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, (∏ τ : X.Ψ, ‖dmin X.Gm (rmul x b) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (rmul x b) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) = (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) ∧ ∀ z ∈ OmF X x0, (∏ τ : X.Ψ, ‖dmin X.Gm (cpt X x0 z) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (cpt X x0 z) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) = Real.exp (-rhF X x0 z)) := by
  intro r X x0 h0
  refine ⟨?_, fun x hx => ⟨?_, ?_⟩, fun x _ b hb => ?_, fun z hz => ?_⟩
  · refine Finset.measurable_prod _ fun τ _ => Measurable.div ?_ ?_
    · exact (ExtFPf.cont_dmin X τ _).norm.measurable
    · have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
      exact ((((continuous_const.matrix_mul hm).matrix_submatrix _ _).matrix_det).norm.pow 2).measurable
  · exact Finset.prod_pos fun τ _ => (factor_mem X h0 hx τ).1
  · exact Finset.prod_le_one (fun τ _ => (factor_mem X h0 hx τ).1.le)
      fun τ _ => (factor_mem X h0 hx τ).2
  · exact Finset.prod_congr rfl fun τ _ => factor_rmul X x0 x hb τ _
  · unfold rhF
    rw [neg_neg, Real.exp_sum]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [lminor_cpt X h0, Real.exp_log (norm_pos_iff.mpr (FlowCoefficientBounds.dmin_ne X hz τ _))]
    simp

end GlobalTheory.FramePotential
