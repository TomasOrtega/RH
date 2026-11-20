import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantOrthogonality
import ReciprocityTheory.SemistableReduction.SemiAll
import ReciprocityTheory.SemistableReduction.ShareBall

namespace GlobalTheory.Up.BallExPf

section Mat
open Matrix ReciprocityTheory.MultiplicativeHeights
open scoped ComplexOrder MatrixOrder

/- English proof (translation)
Use `set J := signMat p r with hJdef`. Establish `hJJ : J * J = 1` using `sb_J_mul_J p r`. Establish `hJh : Jᴴ = J` using `sb_J_herm p r`. Use `set S := CFC.sqrt H with hS`. Establish `hSS : S * S = H` using `CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg`.

Establish `hSp : S.PosSemidef` using `Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg H)`. Establish `hSh : Sᴴ = S` using `hSp.1`. Establish `hSu : IsUnit S.det`. Use `isUnit_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations. Use `hH.det_pos` as an intermediate fact.

Rewrite `this` using `[← hSS, det_mul, h0, mul_zero]`. Conclude with `lt_irrefl _ this`. Establish `h1 : (J * S * J).PosSemidef`. Use `hSp.conjTranspose_mul_mul_same J` as an intermediate fact. Rewrite `this` using `[hJh]`. Then use the resulting hypothesis.

Establish `h2 : (S⁻¹).PosSemidef` using `hSp.inv`. Establish `hsq1 : (J * S * J) * (J * S * J) = J * H * J`. Combine the equalities or inequalities in the displayed calculation. Establish `hsq2 : S⁻¹ * S⁻¹ = J * H * J`. Rewrite using `[← Matrix.mul_inv_rev, hSS]`.

Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `he : J * S * J = S⁻¹`. Rewrite using `[← CFC.sqrt_unique hsq1 h1.nonneg, ← CFC.sqrt_unique hsq2 h2.nonneg]`. Establish `hih : (S⁻¹)ᴴ = S⁻¹` using `h2.1`.

Use `⟨S⁻¹, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hih] conv_lhs => rw [show S⁻¹ * J * S⁻¹ = (J * S * J) * J * S⁻¹ by rw [he]]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hih, ← hSS, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSu, Matrix.one_mul, Matrix.mul_nonsing_inv _ hSu]`.
-/
theorem exists_unitary_diag {r p : ℕ} {H : Matrix (Fin r) (Fin r) ℂ} (hH : H.PosDef)
    (hJ : H * signMat p r * H = signMat p r) :
    ∃ g : Matrix (Fin r) (Fin r) ℂ, gᴴ * signMat p r * g = signMat p r ∧ gᴴ * H * g = 1 := by
  set J := signMat p r with hJdef
  have hJJ : J * J = 1 := sb_J_mul_J p r
  have hJh : Jᴴ = J := sb_J_herm p r
  set S := CFC.sqrt H with hS
  have hSS : S * S = H := CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg
  have hSp : S.PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg H)
  have hSh : Sᴴ = S := hSp.1
  have hSu : IsUnit S.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have := hH.det_pos
    rw [← hSS, det_mul, h0, mul_zero] at this
    exact lt_irrefl _ this
  have h1 : (J * S * J).PosSemidef := by
    have := hSp.conjTranspose_mul_mul_same J
    rwa [hJh] at this
  have h2 : (S⁻¹).PosSemidef := hSp.inv
  have hsq1 : (J * S * J) * (J * S * J) = J * H * J := by
    calc (J * S * J) * (J * S * J) = J * S * (J * J) * S * J := by simp only [Matrix.mul_assoc]
      _ = J * H * J := by rw [hJJ, Matrix.mul_one, ← hSS]; simp only [Matrix.mul_assoc]
  have hsq2 : S⁻¹ * S⁻¹ = J * H * J := by
    rw [← Matrix.mul_inv_rev, hSS]
    apply Matrix.inv_eq_right_inv
    calc H * (J * H * J) = (H * J * H) * J := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hJJ]
  have he : J * S * J = S⁻¹ := by
    rw [← CFC.sqrt_unique hsq1 h1.nonneg, ← CFC.sqrt_unique hsq2 h2.nonneg]
  have hih : (S⁻¹)ᴴ = S⁻¹ := h2.1
  refine ⟨S⁻¹, ?_, ?_⟩
  · rw [hih]
    conv_lhs => rw [show S⁻¹ * J * S⁻¹ = (J * S * J) * J * S⁻¹ by rw [he]]
    calc J * S * J * J * S⁻¹ = J * S * (J * J) * S⁻¹ := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hJJ, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_right _ _ hSu]
  · rw [hih, ← hSS, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSu, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hSu]

/- English proof (translation)
Establish `hJJ` using `sb_J_mul_J p r`. Establish `hPu : IsUnit P.det` using `isUnit_iff_ne_zero.2 hP`. Establish `hH' : (Pᴴ * H * P).PosDef` using `hH.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hPu))`. Establish `hAi : A⁻¹ = P * signMat p r * Pᴴ`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises.

Establish `: signMat p r * (Pᴴ * A * P) = 1` using `by rw [hPA, hJJ]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]`. Use `_ = 1 := by rw [this, Matrix.mul_one, Matrix.mul_nonsing_inv _ hPu]`. Take `⟨g, hg1, hg2⟩` from `exists_unitary_diag (p := p) hH' (by`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [← hAi, hA, hPA])`. Use `⟨P * g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hg1, ← hPA, conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← hg2, conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem exists_frame {r p : ℕ} {H A P : Matrix (Fin r) (Fin r) ℂ} (hH : H.PosDef)
    (hA : H * A⁻¹ * H = A) (hP : P.det ≠ 0) (hPA : Pᴴ * A * P = signMat p r) :
    ∃ x : Matrix (Fin r) (Fin r) ℂ, xᴴ * A * x = signMat p r ∧ xᴴ * H * x = 1 := by
  have hJJ := sb_J_mul_J p r
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  have hH' : (Pᴴ * H * P).PosDef := hH.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hPu))
  have hAi : A⁻¹ = P * signMat p r * Pᴴ := by
    apply Matrix.inv_eq_left_inv
    have : signMat p r * (Pᴴ * A * P) = 1 := by rw [hPA, hJJ]
    calc P * signMat p r * Pᴴ * A = P * (signMat p r * (Pᴴ * A * P)) * P⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]
      _ = 1 := by rw [this, Matrix.mul_one, Matrix.mul_nonsing_inv _ hPu]
  obtain ⟨g, hg1, hg2⟩ := exists_unitary_diag (p := p) hH' (by
    calc Pᴴ * H * P * signMat p r * (Pᴴ * H * P) = Pᴴ * (H * (P * signMat p r * Pᴴ) * H) * P := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [← hAi, hA, hPA])
  refine ⟨P * g, ?_, ?_⟩
  · rw [← hg1, ← hPA, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  · rw [← hg2, conjTranspose_mul]; simp only [Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[hq, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star, sb_re_star_dot]`.
-/
theorem hq_ct_mul {r : ℕ} (Q : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) :
    hq (Qᴴ * Q) u = normSq (Q *ᵥ u) := by
  rw [hq, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star, sb_re_star_dot]

/- English proof (translation)
Use `set A : Matrix (Fin p) (Fin p) ℂ := g.submatrix (Fin.castLE h) (Fin.castLE h) with hA`. Use `set C : Matrix (Fin n) (Fin p) ℂ := Matrix.of fun k a => if (k : ℕ) < p then 0 else g k (Fin.castLE h a) with hC`. Establish `key : Aᴴ * A = 1 + Cᴴ * C`. Use extensionality with `a b`. Establish `e` using `congrFun (congrFun hg (Fin.castLE h a)) (Fin.castLE h b)`.

Rewrite `e` using `[Matrix.mul_apply]`. Simplify using `only [signMat, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply, Fin.castLE_inj] at e`. Establish `e1 : (1 : Matrix (Fin p) (Fin p) ℂ) a b = ∑ k, star (g k (Fin.castLE h a)) * sgn p k * g k (Fin.castLE h b)`. Rewrite using `[e, Matrix.one_apply]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using `[sgn]`. Rewrite using `[if_neg hab, if_neg hab]`. Establish `e2 : (Aᴴ * A) a b = ∑ k : Fin n, if (k : ℕ) < p then starRingEnd ℂ (g k (Fin.castLE h a)) * g k (Fin.castLE h b) else 0`. Rewrite using `[Matrix.mul_apply]`.

Use `Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun k hk => ?_) (fun k => ?_)` and prove the remaining obligations. Rewrite using `[if_neg]`. Introduce `hlt`. Conclude with `hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩`. Simplify using `[hA, Matrix.conjTranspose_apply]`.

Rewrite using `[e2, Matrix.add_apply, e1, Matrix.mul_apply, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : (k : ℕ) < p`. Simplify using `[hC, sgn, hk, Matrix.conjTranspose_apply]`. Simplify using `[hC, sgn, hk, Matrix.conjTranspose_apply]`.

Establish `h1` using `ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_det_one_add_ge (Matrix.posSemidef_conjTranspose_mul_self C)`. Rewrite `h1` using `[← key, ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_normSq_det, ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_trace_ctm]`. Establish `h2 : ∑ a, ∑ b, ‖(sbDn p n * g * sbDp p n) a b‖ ^ 2 = ReciprocityTheory.ChartRestriction.G.AR.Up.sumBdFsq C`. Unfold `ReciprocityTheory.ChartRestriction.G.AR.Up.sumBdFsq`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun b hb => ?_) (fun b => ?_)` and prove the remaining obligations. Establish `: ¬ (b : ℕ) < p` using `fun hlt => hb ⟨⟨b, hlt⟩, Fin.ext rfl⟩`. Simplify using `[sbDn, sbDp, Matrix.mul_diagonal, this]`. Apply the tactic sequence `by_cases hk : (k : ℕ) < p <;>`.

Simplify using `[sbDn, sbDp, Matrix.mul_diagonal, Matrix.diagonal_mul, hC, hk, Complex.normSq_eq_norm_sq]`. Rewrite using `[h2, ← Complex.normSq_eq_norm_sq]`. Conclude with `h1`.
-/
theorem one_add_le_lminor_sq {n p : ℕ} (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : gᴴ * signMat p n * g = signMat p n) :
    1 + ∑ a, ∑ b, ‖(sbDn p n * g * sbDp p n) a b‖ ^ 2 ≤
      ‖ReciprocityTheory.ChartRestriction.G.FD.lminor g ⟨p, Nat.lt_succ_of_le h⟩‖ ^ 2 := by
  set A : Matrix (Fin p) (Fin p) ℂ := g.submatrix (Fin.castLE h) (Fin.castLE h) with hA
  set C : Matrix (Fin n) (Fin p) ℂ :=
    Matrix.of fun k a => if (k : ℕ) < p then 0 else g k (Fin.castLE h a) with hC
  have key : Aᴴ * A = 1 + Cᴴ * C := by
    ext a b
    have e := congrFun (congrFun hg (Fin.castLE h a)) (Fin.castLE h b)
    rw [Matrix.mul_apply] at e
    simp only [signMat, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply, Fin.castLE_inj] at e
    have e1 : (1 : Matrix (Fin p) (Fin p) ℂ) a b =
        ∑ k, star (g k (Fin.castLE h a)) * sgn p k * g k (Fin.castLE h b) := by
      rw [e, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp [sgn]
      · rw [if_neg hab, if_neg hab]
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
    · simp [hC, sgn, hk, Matrix.conjTranspose_apply]
    · simp [hC, sgn, hk, Matrix.conjTranspose_apply]
  have h1 := ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_det_one_add_ge (Matrix.posSemidef_conjTranspose_mul_self C)
  rw [← key, ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_normSq_det, ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_trace_ctm] at h1
  have h2 : ∑ a, ∑ b, ‖(sbDn p n * g * sbDp p n) a b‖ ^ 2 = ReciprocityTheory.ChartRestriction.G.AR.Up.sumBdFsq C := by
    unfold ReciprocityTheory.ChartRestriction.G.AR.Up.sumBdFsq
    refine Finset.sum_congr rfl fun k _ => ?_
    symm
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun b hb => ?_)
      (fun b => ?_)
    · have : ¬ (b : ℕ) < p := fun hlt => hb ⟨⟨b, hlt⟩, Fin.ext rfl⟩
      simp [sbDn, sbDp, Matrix.mul_diagonal, this]
    · by_cases hk : (k : ℕ) < p <;>
        simp [sbDn, sbDp, Matrix.mul_diagonal, Matrix.diagonal_mul, hC, hk, Complex.normSq_eq_norm_sq]
  rw [h2, ← Complex.normSq_eq_norm_sq]
  exact h1

/- English proof (translation)
Use `set J := signMat p n with hJdef`. Establish `hJJ : J * J = 1` using `sb_J_mul_J p n`. Establish `hJh : Jᴴ = J` using `sb_J_herm p n`. Establish `hinv : g⁻¹ = J * gᴴ * J`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Establish `hgu : IsUnit g.det`. Use `isUnit_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations. Establish `e` using `congrArg det hg`. Establish `e2` using `congrArg det hJJ`.

Rewrite `e` using `[det_mul, h0, mul_zero]`. Rewrite `e2` using `[det_mul, ← e, det_one]`. Simplify using `at e2`. Establish `hinvH : (g⁻¹)ᴴ = J * g * J`. Rewrite using `[hinv, conjTranspose_mul, conjTranspose_mul, hJh, conjTranspose_conjTranspose, Matrix.mul_assoc]`.

Use `set c := ∑ a, ∑ b, ‖(sbDn p n * g * sbDp p n) a b‖ ^ 2 with hc`. Establish `hc0 : 0 ≤ c` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _`. Establish `hc1` using `one_add_le_lminor_sq h g hg`. Rewrite `hc1` using `[← hc]`. Establish `hcs : c ≤ s ^ 2 * (1 + c)`.

Rewrite `hl` using `[one_div, Real.log_inv, neg_neg]`. Establish `a1 : Real.log (1 + c) ≤ s ^ 2` using `(Real.log_le_log (by linarith) hc1).trans hl`. Establish `a2` using `Real.one_sub_inv_le_log_of_pos (show 0 < 1 + c by linarith)`. Establish `a3 : 1 - (1 + c)⁻¹ = c / (1 + c)` using `by field_simp; ring`. Rewrite `a2` using `[a3]`.

Conclude with `(div_le_iff₀ (by linarith)).1 (a2.trans a1)`. Establish `hB` using `boundedBall_holds n p ((g⁻¹)ᴴ * g⁻¹) s (Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hgu)))) (by`. Rewrite using `[← hJdef, hinvH]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = J * g * (J * J) * g⁻¹ := by`. Rewrite using `[hJJ, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_right _ _ hgu]`. Simplify using `only [Matrix.mul_assoc, hJJ]`. Use `_ = J := by rw [hJJ, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_right _ _ hgu])`. Use `hs0 hs1 (by`.

Introduce `v hv`. Use `set w := g⁻¹ *ᵥ v with hw`. Establish `hvw : g *ᵥ w = v` using `by rw [hw, mulVec_mulVec, Matrix.mul_nonsing_inv _ hgu, one_mulVec]`. Establish `hJw : J *ᵥ w = w`. Rewrite `hv` using `[← hJdef, ← mulVec_mulVec, ← hw, hinvH, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]`.

Use `congrArg (fun y => g⁻¹ *ᵥ y) hv` as an intermediate fact. Simplify `this` using `only [mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_left _ _ hgu, ← hw]`. Establish `hDw : sbDp p n *ᵥ w = w`. Use function extensionality and compare the values at `k`. Use `congrFun hJw k` as an intermediate fact.

Simplify using `only [hJdef, signMat, mulVec_diagonal, sgn, sbDp] at this ⊢`. Use `split_ifs at this ⊢`. Simplify using the standard rewrite rules. Take the linear combination `(1 / 2 : ℂ) * this`. Establish `b1 : negSq p v ≤ c * normSq w`.

Rewrite using `[sb_negSq_eq, ← hvw]`. Use `conv_lhs => rw [← hDw, mulVec_mulVec, mulVec_mulVec]`. Conclude with `sb_normSq_mulVec_le _ _`. Establish `b2 : posSq p v - negSq p v = normSq w`. Rewrite using `[← sb_re_dot_J, ← hJdef, ← sb_re_star_dot]`.

Use `conv_rhs => rw [show star w ⬝ᵥ w = star w ⬝ᵥ ((gᴴ * J * g) *ᵥ w) by rw [hg, hJw]]`. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, hvw, dotProduct_mulVec (star w), vecMul_conjTranspose, star_star, hvw]`. Establish `b3 : 0 ≤ normSq w` using `sb_normSq_nonneg w`. Establish `b4 : 0 ≤ posSq p v` using `by rw [sb_posSq_eq]; exact sb_normSq_nonneg _`. Establish `b5 : negSq p v * (1 + c) ≤ s ^ 2 * posSq p v * (1 + c)`.

Use `mul_le_mul_of_nonneg_right hcs b4` as an intermediate fact. Rewrite `b1` using `[← b2]`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `le_of_mul_le_mul_right b5 (by linarith))`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `(hB u).1` as an intermediate fact. Rewrite `this` using `[hq_ct_mul]`. Then use the resulting hypothesis. Use `(hB (g *ᵥ u)).2` as an intermediate fact. Rewrite `this` using `[hq_ct_mul, mulVec_mulVec, Matrix.nonsing_inv_mul _ hgu, one_mulVec]`. Then use the resulting hypothesis.
-/
theorem norm_bound {n p : ℕ} (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : gᴴ * signMat p n * g = signMat p n) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hl : -Real.log (1 / ‖ReciprocityTheory.ChartRestriction.G.FD.lminor g ⟨p, Nat.lt_succ_of_le h⟩‖ ^ 2) ≤ s ^ 2)
    (u : Fin n → ℂ) :
    normSq (g⁻¹ *ᵥ u) ≤ (1 + s) / (1 - s) * normSq u ∧
      normSq (g *ᵥ u) ≤ (1 + s) / (1 - s) * normSq u := by
  set J := signMat p n with hJdef
  have hJJ : J * J = 1 := sb_J_mul_J p n
  have hJh : Jᴴ = J := sb_J_herm p n
  have hinv : g⁻¹ = J * gᴴ * J := by
    apply Matrix.inv_eq_left_inv
    calc J * gᴴ * J * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, hJJ]
  have hgu : IsUnit g.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have e := congrArg det hg
    have e2 := congrArg det hJJ
    rw [det_mul, h0, mul_zero] at e
    rw [det_mul, ← e, det_one] at e2
    simp at e2
  have hinvH : (g⁻¹)ᴴ = J * g * J := by
    rw [hinv, conjTranspose_mul, conjTranspose_mul, hJh, conjTranspose_conjTranspose, Matrix.mul_assoc]
  set c := ∑ a, ∑ b, ‖(sbDn p n * g * sbDp p n) a b‖ ^ 2 with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc1 := one_add_le_lminor_sq h g hg
  rw [← hc] at hc1
  have hcs : c ≤ s ^ 2 * (1 + c) := by
    rw [one_div, Real.log_inv, neg_neg] at hl
    have a1 : Real.log (1 + c) ≤ s ^ 2 := (Real.log_le_log (by linarith) hc1).trans hl
    have a2 := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + c by linarith)
    have a3 : 1 - (1 + c)⁻¹ = c / (1 + c) := by field_simp; ring
    rw [a3] at a2
    exact (div_le_iff₀ (by linarith)).1 (a2.trans a1)
  have hB := boundedBall_holds n p ((g⁻¹)ᴴ * g⁻¹) s
    (Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hgu))))
    (by
      rw [← hJdef, hinvH]
      calc J * g * J * g⁻¹ * J * (J * g * J * g⁻¹) = J * g * J * g⁻¹ * (J * J) * g * J * g⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = J * g * (J * J) * g⁻¹ := by
            rw [hJJ, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_right _ _ hgu]
            simp only [Matrix.mul_assoc, hJJ]
        _ = J := by rw [hJJ, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_right _ _ hgu])
    hs0 hs1 (by
      intro v hv
      set w := g⁻¹ *ᵥ v with hw
      have hvw : g *ᵥ w = v := by rw [hw, mulVec_mulVec, Matrix.mul_nonsing_inv _ hgu, one_mulVec]
      have hJw : J *ᵥ w = w := by
        rw [← hJdef, ← mulVec_mulVec, ← hw, hinvH, mulVec_mulVec, ← Matrix.mul_assoc,
          ← Matrix.mul_assoc, hJJ, Matrix.one_mul] at hv
        have := congrArg (fun y => g⁻¹ *ᵥ y) hv
        simpa only [mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_left _ _ hgu, ← hw] using this
      have hDw : sbDp p n *ᵥ w = w := by
        funext k
        have := congrFun hJw k
        simp only [hJdef, signMat, mulVec_diagonal, sgn, sbDp] at this ⊢
        split_ifs at this ⊢
        · simp
        · linear_combination (1 / 2 : ℂ) * this
      have b1 : negSq p v ≤ c * normSq w := by
        rw [sb_negSq_eq, ← hvw]
        conv_lhs => rw [← hDw, mulVec_mulVec, mulVec_mulVec]
        exact sb_normSq_mulVec_le _ _
      have b2 : posSq p v - negSq p v = normSq w := by
        rw [← sb_re_dot_J, ← hJdef, ← sb_re_star_dot]
        conv_rhs => rw [show star w ⬝ᵥ w = star w ⬝ᵥ ((gᴴ * J * g) *ᵥ w) by rw [hg, hJw]]
        rw [← mulVec_mulVec, ← mulVec_mulVec, hvw, dotProduct_mulVec (star w), vecMul_conjTranspose,
          star_star, hvw]
      have b3 : 0 ≤ normSq w := sb_normSq_nonneg w
      have b4 : 0 ≤ posSq p v := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
      have b5 : negSq p v * (1 + c) ≤ s ^ 2 * posSq p v * (1 + c) := by
        have := mul_le_mul_of_nonneg_right hcs b4
        rw [← b2] at b1
        nlinarith
      exact le_of_mul_le_mul_right b5 (by linarith))
  refine ⟨?_, ?_⟩
  · have := (hB u).1
    rwa [hq_ct_mul] at this
  · have := (hB (g *ᵥ u)).2
    rwa [hq_ct_mul, mulVec_mulVec, Matrix.nonsing_inv_mul _ hgu, one_mulVec] at this

/- English proof (translation)
Unfold `hq`. Rewrite using `[← Complex.conj_re (star u ⬝ᵥ _)]`. Use `congr 1`. Simplify using `[dotProduct, mulVec, map_sum]`.
-/
theorem hq_conj {r : ℕ} (H : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) :
    hq (H.map (starRingEnd ℂ)) (star u) = hq H u := by
  unfold hq
  rw [← Complex.conj_re (star u ⬝ᵥ _)]
  congr 1
  simp [dotProduct, mulVec, map_sum]

end Mat

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Establish `e1 : (gram τ X.Gm M)ᵀ = Mᴴ * (MajorantOrthogonality.pform X).G.map τ * M`. Rewrite using `[FrameDegreeData.gram_eq, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`. Both sides reduce to the same expression. Establish `e2 : (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))ᵀ = ReciprocityTheory.MultiplicativeHeights.signMat X.p0 r`. Rewrite using `[Matrix.diagonal_transpose, ReciprocityTheory.MultiplicativeHeights.signMat]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `only [sgn, ReciprocityTheory.MultiplicativeHeights.sgn]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[← e1, ← e2, Matrix.transpose_inj]`.
-/
theorem gram_iff (X : Data E r) (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ X.Gm M = (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ↔
      Mᴴ * (MajorantOrthogonality.pform X).G.map τ * M = ReciprocityTheory.MultiplicativeHeights.signMat X.p0 r := by
  have e1 : (gram τ X.Gm M)ᵀ = Mᴴ * (MajorantOrthogonality.pform X).G.map τ * M := by
    rw [FrameDegreeData.gram_eq, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
    rfl
  have e2 : (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))ᵀ =
      ReciprocityTheory.MultiplicativeHeights.signMat X.p0 r := by
    rw [Matrix.diagonal_transpose, ReciprocityTheory.MultiplicativeHeights.signMat]
    congr 1
    funext a
    simp only [sgn, ReciprocityTheory.MultiplicativeHeights.sgn]
    split_ifs <;> simp
  rw [← e1, ← e2, Matrix.transpose_inj]

/- English proof (translation)
Establish `hr1 : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hu : IsUnit (mat x0 τ).det` using `isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)`. Use `norm_bound X.p0_le _ ?_ (by positivity) ?_ ?_ u` and prove the remaining obligations. Establish `a0` using `(gram_iff X τ.1 _).1 (h0 τ)`. Establish `a1` using `(gram_iff X τ.1 _).1 (h1 τ)`.

Use `conv_lhs => rw [← a0]`. Rewrite using `[← a1]`. Use `conv_rhs => rw [← Matrix.mul_nonsing_inv_cancel_left _ (mat x1 τ) hu, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[div_lt_one (by positivity)]; linarith`.

Use `neg_log_factor_le_rhX h0 (IW.orth_mem_dom X x1 h1) τ` as an intermediate fact. Rewrite `this` using `[FramePotential.norm_dmin_of_isOrth X h1]`. Use `this.trans (hρ.le.trans (le_of_eq ?_))` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Evaluate the numerical expressions.
-/
theorem frame_bound (hr : 0 < r) (X : Data E r) {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0)
    (h1 : IsOrth X x1) (hρ : rhX X x0 x1 < 1 / (49 * (r : ℝ) ^ 2)) (τ : X.Ψ) (u : Fin r → ℂ) :
    ReciprocityTheory.MultiplicativeHeights.normSq (((mat x0 τ)⁻¹ * mat x1 τ)⁻¹ *ᵥ u) ≤
        ReciprocityTheory.MultiplicativeHeights.ballRatio r * ReciprocityTheory.MultiplicativeHeights.normSq u ∧
      ReciprocityTheory.MultiplicativeHeights.normSq (((mat x0 τ)⁻¹ * mat x1 τ) *ᵥ u) ≤
        ReciprocityTheory.MultiplicativeHeights.ballRatio r * ReciprocityTheory.MultiplicativeHeights.normSq u := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)
  refine norm_bound X.p0_le _ ?_ (by positivity) ?_ ?_ u
  · have a0 := (gram_iff X τ.1 _).1 (h0 τ)
    have a1 := (gram_iff X τ.1 _).1 (h1 τ)
    conv_lhs => rw [← a0]
    rw [← a1]
    conv_rhs => rw [← Matrix.mul_nonsing_inv_cancel_left _ (mat x1 τ) hu, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  · rw [div_lt_one (by positivity)]; linarith
  · have := neg_log_factor_le_rhX h0 (IW.orth_mem_dom X x1 h1) τ
    rw [FramePotential.norm_dmin_of_isOrth X h1] at this
    refine this.trans (hρ.le.trans (le_of_eq ?_))
    field_simp
    norm_num

end GlobalTheory.Up.BallExPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory.Up
open BallExPf

end GlobalTheory.Up
