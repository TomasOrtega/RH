import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.SumInnerBasisSqEqAdjoint
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PBridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

open CompactHaarProbability in
/- English proof (translation)
Rewrite using `[fF_eq_integral, fF_eq_integral]`. Establish `h1 : ∀ (c : ℂ) (I : T.V →L[ℂ] T.V), T.op k⁻¹ * (c • I) * T.op k = c • conjE T k⁻¹ I`. Introduce `c I`. Rewrite using `[conjE_apply, inv_inv, mul_smul_comm, smul_mul_assoc]`. Rewrite using `[h1, ← ContinuousLinearEquiv.integral_comp_comm]`.

Use `congr 1`. Use `conv_rhs => rw [← integral_mul_left_eq_self _ k]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `hm : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b` using `fun _ _ => rfl`. Establish `he : toMK (k * x)⁻¹ * pmat z * toMK (k * x) = toMK x⁻¹ * (toMK k⁻¹ * pmat z * toMK k) * toMK x`.

Rewrite using `[_root_.mul_inv_rev, hm, hm]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hop : T.op k⁻¹ * (T.op (k * x) * projW T * T.op (k * x)⁻¹) * T.op k = T.op x * projW T * T.op x⁻¹`. Rewrite using `[_root_.mul_inv_rev, op_mul, op_mul]`. Simplify using `only [mul_assoc]`.

Rewrite using `[op_inv_mul, mul_one, ← mul_assoc (T.op k⁻¹), op_inv_mul, one_mul]`. Use `beta_reduce`. Rewrite using `[conjE_apply, inv_inv, mul_smul_comm, smul_mul_assoc, he, hop]`.
-/
theorem fF_conj_pmat_eq_op_inv_mul_fF_mul_op {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : KType ε (lowK ε lam)) (k : KG ε) (z : PCoord ε → ℂ) :
    fF ε lam T (toMK k⁻¹ * pmat z * toMK k) = T.op k⁻¹ * fF ε lam T (pmat z) * T.op k := by
  rw [fF_eq_integral, fF_eq_integral]
  have h1 : ∀ (c : ℂ) (I : T.V →L[ℂ] T.V), T.op k⁻¹ * (c • I) * T.op k = c • conjE T k⁻¹ I := by
    intro c I
    rw [conjE_apply, inv_inv, mul_smul_comm, smul_mul_assoc]
  rw [h1, ← ContinuousLinearEquiv.integral_comp_comm]
  congr 1
  conv_rhs => rw [← integral_mul_left_eq_self _ k]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hm : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := fun _ _ => rfl
  have he : toMK (k * x)⁻¹ * pmat z * toMK (k * x) = toMK x⁻¹ * (toMK k⁻¹ * pmat z * toMK k) * toMK x := by
    rw [_root_.mul_inv_rev, hm, hm]
    simp only [Matrix.mul_assoc]
  have hop : T.op k⁻¹ * (T.op (k * x) * projW T * T.op (k * x)⁻¹) * T.op k = T.op x * projW T * T.op x⁻¹ := by
    rw [_root_.mul_inv_rev, op_mul, op_mul]
    simp only [mul_assoc]
    rw [op_inv_mul, mul_one, ← mul_assoc (T.op k⁻¹), op_inv_mul, one_mul]
  beta_reduce
  rw [conjE_apply, inv_inv, mul_smul_comm, smul_mul_assoc, he, hop]

/- English proof (translation)
Unfold `hsOp`. Use `set b := stdOrthonormalBasis ℂ V`. Establish `h1 : ∀ i, ‖(ContinuousLinearMap.adjoint A) (b i)‖ ^ 2 = ∑ j, ‖⟪b i, A (b j)⟫_ℂ‖ ^ 2`. Introduce `i`. Rewrite using `[← b.sum_sq_norm_inner_right]`.

Use `sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]`. Establish `h2 : ∀ j, ‖A (b j)‖ ^ 2 = ∑ i, ‖⟪b i, A (b j)⟫_ℂ‖ ^ 2` using `fun j => (b.sum_sq_norm_inner_right _).symm`. Repeatedly rewrite using `[h1, h2]`. Conclude with `sum_comm`.
-/
theorem sum_norm_adjoint_sq_eq_hsOp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [CompleteSpace V] (A : V →L[ℂ] V) :
    ∑ i, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V i)‖ ^ 2 = hsOp A := by
  unfold hsOp
  set b := stdOrthonormalBasis ℂ V
  have h1 : ∀ i, ‖(ContinuousLinearMap.adjoint A) (b i)‖ ^ 2 = ∑ j, ‖⟪b i, A (b j)⟫_ℂ‖ ^ 2 := by
    intro i
    rw [← b.sum_sq_norm_inner_right]
    refine sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
  have h2 : ∀ j, ‖A (b j)‖ ^ 2 = ∑ i, ‖⟪b i, A (b j)⟫_ℂ‖ ^ 2 := fun j => (b.sum_sq_norm_inner_right _).symm
  simp_rw [h1, h2]
  exact sum_comm

/- English proof (translation)
Use `set b := stdOrthonormalBasis ℂ T.V`. Use `set B := ContinuousLinearMap.adjoint A`. Establish `hc : Continuous fun k : KG ε => T.op k T.w` using `(KType_continuous_op T).clm_apply continuous_const`. Establish `hpt : ∀ k : KG ε, ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2 ≤ ∑ i, ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2`. Introduce `k`.

Establish `hn : ‖T.op k T.w‖ = 1` using `by rw [KType_norm_op_apply, T.w_norm]`. Establish `e : ∑ i, ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2 = ‖A (T.op k T.w)‖ ^ 2`. Rewrite using `[← b.sum_sq_norm_inner_right]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.adjoint_inner_left]`.

Rewrite using `[e]`. Use `norm_inner_le_norm (𝕜 := ℂ) (T.op k T.w) (A (T.op k T.w))` as an intermediate fact. Rewrite `this` using `[hn, one_mul]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) this 2`. Establish `hI1 : Integrable (fun k : KG ε => ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2) (dk ε)` using `integrable_dk_of_continuous ((continuous_inner.comp (hc.prodMk (A.continuous.comp hc))).norm.pow 2)`.

Establish `hI2 : ∀ i, Integrable (fun k : KG ε => ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2) (dk ε)` using `fun i => integrable_dk_of_continuous ((continuous_const.inner hc).norm.pow 2)`. Establish `hmono` using `integral_mono hI1 (integrable_finsetSum _ fun i _ => hI2 i) hpt`. Rewrite `hmono` using `[integral_finsetSum _ fun i _ => hI2 i]`. Establish `hd : (0 : ℝ) ≤ Module.finrank ℂ T.V` using `Nat.cast_nonneg _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_sum]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[kschur_coef, T.w_norm, one_pow, one_mul]`. Use `_ = hsOp A := sum_norm_adjoint_sq_eq_hsOp A`.
-/
theorem hsOp_ge_integral {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (A : T.V →L[ℂ] T.V) :
    (Module.finrank ℂ T.V : ℝ) * ∫ k, ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2 ∂(dk ε) ≤ hsOp A := by
  set b := stdOrthonormalBasis ℂ T.V
  set B := ContinuousLinearMap.adjoint A
  have hc : Continuous fun k : KG ε => T.op k T.w := (KType_continuous_op T).clm_apply continuous_const
  have hpt : ∀ k : KG ε, ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2 ≤ ∑ i, ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2 := by
    intro k
    have hn : ‖T.op k T.w‖ = 1 := by rw [KType_norm_op_apply, T.w_norm]
    have e : ∑ i, ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2 = ‖A (T.op k T.w)‖ ^ 2 := by
      rw [← b.sum_sq_norm_inner_right]
      refine sum_congr rfl fun i _ => ?_
      rw [ContinuousLinearMap.adjoint_inner_left]
    rw [e]
    have := norm_inner_le_norm (𝕜 := ℂ) (T.op k T.w) (A (T.op k T.w))
    rw [hn, one_mul] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hI1 : Integrable (fun k : KG ε => ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2) (dk ε) :=
    integrable_dk_of_continuous ((continuous_inner.comp (hc.prodMk (A.continuous.comp hc))).norm.pow 2)
  have hI2 : ∀ i, Integrable (fun k : KG ε => ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2) (dk ε) := fun i =>
    integrable_dk_of_continuous ((continuous_const.inner hc).norm.pow 2)
  have hmono := integral_mono hI1 (integrable_finsetSum _ fun i _ => hI2 i) hpt
  rw [integral_finsetSum _ fun i _ => hI2 i] at hmono
  have hd : (0 : ℝ) ≤ Module.finrank ℂ T.V := Nat.cast_nonneg _
  calc (Module.finrank ℂ T.V : ℝ) * ∫ k, ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2 ∂(dk ε)
      ≤ (Module.finrank ℂ T.V : ℝ) * ∑ i, ∫ k, ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2 ∂(dk ε) :=
        mul_le_mul_of_nonneg_left hmono hd
    _ = ∑ i, ‖B (b i)‖ ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [kschur_coef, T.w_norm, one_pow, one_mul]
    _ = hsOp A := sum_norm_adjoint_sq_eq_hsOp A

open CompactHaarProbability in
/- English proof (translation)
Establish `hf : Continuous (fun p : (PCoord ε → ℂ) × KG ε => ((Real.exp (-Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2)) : ℝ) : ℂ) • (T.op p.2 * projW T * T.op p.2⁻¹))` using `(Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_potential_conj_prod lam).neg)).smul ((cont_conj T _).comp continuous_snd)`. Establish `h2` using `continuous_parametric_integral_of_continuous (μ := dk ε) (f := fun z k => ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹)) hf isCompact_univ`. Simplify using `only [Measure.restrict_univ] at h2`. Establish `he : (fun z : PCoord ε → ℂ => fF ε lam T (pmat z)) = fun z => ((Module.finrank ℂ T.V : ℝ) : ℂ) • ∫ k, ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹) ∂(dk ε)`. Use function extensionality and compare the values at `fun z => fF_eq_integral lam T _`.

Rewrite using `[he]`. Conclude with `(continuous_const : Continuous fun _ : PCoord ε → ℂ => ((Module.finrank ℂ T.V : ℝ) : ℂ)).smul h2`.
-/
theorem continuous_fF (ε : Fin n → Bool) (lam : Fin n → ℝ) {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Continuous fun z : PCoord ε → ℂ => fF ε lam T (pmat z) := by
  have hf : Continuous (fun p : (PCoord ε → ℂ) × KG ε =>
      ((Real.exp (-Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2)) : ℝ) : ℂ) • (T.op p.2 * projW T * T.op p.2⁻¹)) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_potential_conj_prod lam).neg)).smul
      ((cont_conj T _).comp continuous_snd)
  have h2 := continuous_parametric_integral_of_continuous (μ := dk ε)
    (f := fun z k => ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹))
    hf isCompact_univ
  simp only [Measure.restrict_univ] at h2
  have he : (fun z : PCoord ε → ℂ => fF ε lam T (pmat z)) = fun z => ((Module.finrank ℂ T.V : ℝ) : ℂ) •
      ∫ k, ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹) ∂(dk ε) :=
    funext fun z => fF_eq_integral lam T _
  rw [he]
  exact (continuous_const : Continuous fun _ : PCoord ε → ℂ => ((Module.finrank ℂ T.V : ℝ) : ℂ)).smul h2

/- English proof (translation)
Rewrite using `[← conj_pmat_eq_adK, fF_conj_pmat_eq_op_inv_mul_fF_mul_op, KType_op_inv_eq_adjoint, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right]`.
-/
theorem inner_fF_conj {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : KType ε (lowK ε lam)) (k : KG ε)
    (z : PCoord ε → ℂ) :
    ⟪T.w, fF ε lam T (pmat (adK k⁻¹ z)) T.w⟫_ℂ = ⟪T.op k T.w, fF ε lam T (pmat z) (T.op k T.w)⟫_ℂ := by
  rw [← conj_pmat_eq_adK, fF_conj_pmat_eq_op_inv_mul_fF_mul_op, KType_op_inv_eq_adjoint, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_right]

/- English proof (translation)
Establish `hpos : 0 < (Module.finrank ℂ T.V : ℝ)`. Establish `: Nontrivial T.V` using `⟨⟨T.w, 0, fun h => by`. Use `T.w_norm` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`. Conclude with `zero_ne_one this⟩⟩`.

Conclude with `Module.finrank_pos` after adjusting the coercions. Establish `l6` using `lemma6a hF hd`. Use `set D : ℝ := (Module.finrank ℂ T.V : ℝ) with hD`. Use `set G : (PCoord ε → ℂ) → ℝ := fun z => ‖⟪T.w, fF ε lam T (pmat z) T.w⟫_ℂ‖ ^ 2 with hG`. Use `set h : KG ε → (PCoord ε → ℂ) → ℝ := fun k z => ‖⟪T.op k T.w, fF ε lam T (pmat z) (T.op k T.w)⟫_ℂ‖ ^ 2 * Jac z with hh`.

Establish `hFc` using `continuous_fF ε lam T`. Establish `hJc` using `pb_jac_continuous ε`. Establish `hGc : Continuous G` using `(continuous_const.inner (hFc.clm_apply continuous_const)).norm.pow 2`. Establish `hc : Continuous fun k : KG ε => T.op k T.w` using `(KType_continuous_op T).clm_apply continuous_const`. Establish `hhc : Continuous (Function.uncurry h)`.

Establish `a : Continuous fun p : KG ε × (PCoord ε → ℂ) => T.op p.1 T.w` using `hc.comp continuous_fst`. Conclude with `((a.inner ((hFc.comp continuous_snd).clm_apply a)).norm.pow 2).mul (hJc.comp continuous_snd)`. Establish `s1 : ∀ k : KG ε, ∫⁻ z, ENNReal.ofReal (h k z) = ∫⁻ z, ENNReal.ofReal (G z * Jac z)`. Introduce `k`. Establish `hm : Measurable fun z => ENNReal.ofReal (G z * Jac z)` using `ENNReal.measurable_ofReal.comp (hGc.mul hJc).measurable`.

Rewrite using `[← (adK_measurePreserving k⁻¹).lintegral_comp hm]`. Use `lintegral_congr fun z => ?_` and prove the remaining obligations. Simplify using `only [h, G, inner_fF_conj, jac_adK]`. Establish `s2 : ∫⁻ z, ENNReal.ofReal (G z * Jac z) = ∫⁻ z, ∫⁻ k, ENNReal.ofReal (h k z) ∂(dk ε)`. Establish `e : ∫⁻ z, ENNReal.ofReal (G z * Jac z) = ∫⁻ k, (∫⁻ z, ENNReal.ofReal (h k z)) ∂(dk ε)`.

Simplify using `only [s1, lintegral_const, measure_univ, mul_one]`. Rewrite using `[e, lintegral_lintegral_swap (f := fun k z => ENNReal.ofReal (h k z)) (μ := dk ε) (ν := volume) (ENNReal.measurable_ofReal.comp hhc.measurable).aemeasurable]`. Establish `s3 : ∀ z, ENNReal.ofReal D * ∫⁻ k, ENNReal.ofReal (h k z) ∂(dk ε) ≤ ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z)`. Introduce `z`. Establish `hi : Integrable (fun k => ‖⟪T.op k T.w, fF ε lam T (pmat z) (T.op k T.w)⟫_ℂ‖ ^ 2) (dk ε)` using `integrable_dk_of_continuous ((continuous_inner.comp (hc.prodMk ((fF ε lam T (pmat z)).continuous.comp hc))).norm.pow 2)`.

Rewrite using `[← ofReal_integral_eq_lintegral_ofReal (hi.mul_const _) (Filter.Eventually.of_forall fun k => mul_nonneg (by positivity) (jacobian_nonneg z)), integral_mul_const, ← ENNReal.ofReal_mul hpos.le, ← mul_assoc]`. Conclude with `ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hsOp_ge_integral T _) (jacobian_nonneg z))`. Establish `s4 : ENNReal.ofReal D * ∫⁻ z, ENNReal.ofReal (G z * Jac z) ≤ ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z)`. Rewrite using `[s2, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Conclude with `lintegral_mono s3`.

Establish `s5 : ENNReal.ofReal D * (ENNReal.ofReal (cPQ ε) * ∫⁻ z, ENNReal.ofReal (G z * Jac z)) ≤ ENNReal.ofReal D * ENNReal.ofReal (D / d)`. Rewrite using `[← ENNReal.ofReal_mul hpos.le, show D * (D / d) = D ^ 2 / d by ring, l6, mul_left_comm]`. Conclude with `mul_le_mul_right s4 _`. Conclude with `(ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top).1 s5`.
-/
theorem formal_degree_inequality {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {T : KType ε (lowK ε lam)}
    {j : T.V →L[ℂ] H} (hF : FData ε lam σ T j) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg (muCD ε) σ d) :
    ENNReal.ofReal (cPQ ε) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪T.w, fF ε lam T (pmat z) T.w⟫_ℂ‖ ^ 2 * Jac z) ≤
      ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) / d) := by
  have hpos : 0 < (Module.finrank ℂ T.V : ℝ) := by
    have : Nontrivial T.V := ⟨⟨T.w, 0, fun h => by
      have := T.w_norm; rw [h, norm_zero] at this; exact zero_ne_one this⟩⟩
    exact_mod_cast Module.finrank_pos
  have l6 := lemma6a hF hd
  set D : ℝ := (Module.finrank ℂ T.V : ℝ) with hD
  set G : (PCoord ε → ℂ) → ℝ := fun z => ‖⟪T.w, fF ε lam T (pmat z) T.w⟫_ℂ‖ ^ 2 with hG
  set h : KG ε → (PCoord ε → ℂ) → ℝ :=
    fun k z => ‖⟪T.op k T.w, fF ε lam T (pmat z) (T.op k T.w)⟫_ℂ‖ ^ 2 * Jac z with hh
  have hFc := continuous_fF ε lam T
  have hJc := pb_jac_continuous ε
  have hGc : Continuous G := (continuous_const.inner (hFc.clm_apply continuous_const)).norm.pow 2
  have hc : Continuous fun k : KG ε => T.op k T.w := (KType_continuous_op T).clm_apply continuous_const
  have hhc : Continuous (Function.uncurry h) := by
    have a : Continuous fun p : KG ε × (PCoord ε → ℂ) => T.op p.1 T.w := hc.comp continuous_fst
    exact ((a.inner ((hFc.comp continuous_snd).clm_apply a)).norm.pow 2).mul (hJc.comp continuous_snd)
  have s1 : ∀ k : KG ε, ∫⁻ z, ENNReal.ofReal (h k z) = ∫⁻ z, ENNReal.ofReal (G z * Jac z) := by
    intro k
    have hm : Measurable fun z => ENNReal.ofReal (G z * Jac z) :=
      ENNReal.measurable_ofReal.comp (hGc.mul hJc).measurable
    rw [← (adK_measurePreserving k⁻¹).lintegral_comp hm]
    refine lintegral_congr fun z => ?_
    simp only [h, G, inner_fF_conj, jac_adK]
  have s2 : ∫⁻ z, ENNReal.ofReal (G z * Jac z) = ∫⁻ z, ∫⁻ k, ENNReal.ofReal (h k z) ∂(dk ε) := by
    have e : ∫⁻ z, ENNReal.ofReal (G z * Jac z) = ∫⁻ k, (∫⁻ z, ENNReal.ofReal (h k z)) ∂(dk ε) := by
      simp only [s1, lintegral_const, measure_univ, mul_one]
    rw [e, lintegral_lintegral_swap (f := fun k z => ENNReal.ofReal (h k z)) (μ := dk ε) (ν := volume)
      (ENNReal.measurable_ofReal.comp hhc.measurable).aemeasurable]
  have s3 : ∀ z, ENNReal.ofReal D * ∫⁻ k, ENNReal.ofReal (h k z) ∂(dk ε) ≤
      ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z) := by
    intro z
    have hi : Integrable (fun k => ‖⟪T.op k T.w, fF ε lam T (pmat z) (T.op k T.w)⟫_ℂ‖ ^ 2) (dk ε) :=
      integrable_dk_of_continuous ((continuous_inner.comp (hc.prodMk ((fF ε lam T (pmat z)).continuous.comp hc))).norm.pow 2)
    rw [← ofReal_integral_eq_lintegral_ofReal (hi.mul_const _)
      (Filter.Eventually.of_forall fun k => mul_nonneg (by positivity) (jacobian_nonneg z)),
      integral_mul_const, ← ENNReal.ofReal_mul hpos.le, ← mul_assoc]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hsOp_ge_integral T _) (jacobian_nonneg z))
  have s4 : ENNReal.ofReal D * ∫⁻ z, ENNReal.ofReal (G z * Jac z) ≤
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z) := by
    rw [s2, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono s3
  have s5 : ENNReal.ofReal D * (ENNReal.ofReal (cPQ ε) * ∫⁻ z, ENNReal.ofReal (G z * Jac z)) ≤
      ENNReal.ofReal D * ENNReal.ofReal (D / d) := by
    rw [← ENNReal.ofReal_mul hpos.le, show D * (D / d) = D ^ 2 / d by ring, l6, mul_left_comm]
    exact mul_le_mul_right s4 _
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top).1 s5

/- English proof (translation)
The claim follows from `formal_degree_inequality hF hd`.
-/
theorem lintegral_fF_coeff_sq_le_finrank_div_fdeg {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {T : KType ε (lowK ε lam)}
    {j : T.V →L[ℂ] H} (hF : FData ε lam σ T j) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg (muCD ε) σ d) :
    ENNReal.ofReal (cPQ ε) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪T.w, fF ε lam T (pmat z) T.w⟫_ℂ‖ ^ 2 * Jac z) ≤
      ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) / d) :=
  formal_degree_inequality hF hd

end ReciprocityTheory.ChartRestriction.DS
