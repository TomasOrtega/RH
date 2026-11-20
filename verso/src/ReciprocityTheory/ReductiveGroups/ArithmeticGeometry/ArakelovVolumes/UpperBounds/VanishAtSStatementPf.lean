import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
  Filter Asymptotics
open scoped ENNReal

noncomputable section

/- English proof (translation)
Take `⟨C, hC⟩` from `hf.hasFDerivAt.isBigO_sub.bound`. Use `⟨C, hC.mono fun z hz => ?_⟩` and prove the remaining obligations. Simplify `hz` using `[h0]`.
-/
theorem bigO_of_diff {n : ℕ} {f : V n → ℂ} (hf : DifferentiableAt ℂ f 0) (h0 : f 0 = 0) :
    ∃ C : ℝ, ∀ᶠ z in 𝓝 (0 : V n), ‖f z‖ ≤ C * ‖z‖ := by
  obtain ⟨C, hC⟩ := hf.hasFDerivAt.isBigO_sub.bound
  refine ⟨C, hC.mono fun z hz => ?_⟩
  simpa [h0] using hz

/- English proof (translation)
Establish `hdiff : DifferentiableAt ℂ σ 0`. Assume the negation of the conclusion as `hnd`. Apply `hdet` to reduce the goal to its premises. Rewrite using `[fderiv_zero_of_not_differentiableAt hnd]`. Simplify using `[ContinuousLinearMap.det, LinearMap.det_zero, hn.ne']`.

Use `set L := fderiv ℂ σ 0 with hL`. Establish `hu : IsUnit (L : V n →ₗ[ℂ] V n)` using `(LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)`. Establish `hbij : Function.Bijective (L : V n →ₗ[ℂ] V n)` using `(Module.End.isUnit_iff _).mp hu`. Set `e : V n ≃L[ℂ] V n` to `(LinearEquiv.ofBijective (L : V n →ₗ[ℂ] V n) hbij).toContinuousLinearEquiv`. Use `set K : ℝ := ‖(e.symm : V n →L[ℂ] V n)‖ + 1 with hKdef`.

Establish `hK : 0 < K` using `by positivity`. Establish `hle : ∀ z, ‖z‖ ≤ K * ‖L z‖`. Introduce `z`. Establish `h1 : (e.symm : V n →L[ℂ] V n) (L z) = z`. Establish `h2 : e z = L z` using `rfl`.

Rewrite using `[← h2, ContinuousLinearEquiv.coe_coe, e.symm_apply_apply]`. Combine the equalities or inequalities in the displayed calculation. Establish `hc0 : (0 : ℝ) < 1 / (2 * K)` using `by positivity`. Establish `hcK : 1 / (2 * K) * K = 1 / 2` using `by field_simp`. Use `⟨1 / (2 * K), hc0, ?_⟩` and prove the remaining obligations.

Establish `ho` using `(hasFDerivAt_iff_isLittleO_nhds_zero.mp hdiff.hasFDerivAt).def hc0`. Use `filter_upwards [ho] with z hz`. Simplify using `only [zero_add, h0, sub_zero] at hz`. Establish `h3 : ‖L z‖ ≤ ‖σ z‖ + ‖σ z - L z‖`. Establish `h4` using `norm_sub_le (σ z) (σ z - L z)`.

Simplify using `using h4`. Establish `h4 : 1 / (2 * K) * ‖z‖ ≤ 1 / (2 * K) * (K * ‖L z‖)` using `mul_le_mul_of_nonneg_left (hle z) hc0.le`. Establish `h5 : 1 / (2 * K) * (K * ‖L z‖) = ‖L z‖ / 2` using `by rw [← mul_assoc, hcK]; ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lower_of_det {n : ℕ} (hn : 0 < n) {σ : V n → V n} (h0 : σ 0 = 0)
    (hdet : (fderiv ℂ σ 0).det ≠ 0) : ∃ c > 0, ∀ᶠ z in 𝓝 (0 : V n), c * ‖z‖ ≤ ‖σ z‖ := by
  have hdiff : DifferentiableAt ℂ σ 0 := by
    by_contra hnd
    apply hdet
    rw [fderiv_zero_of_not_differentiableAt hnd]
    simp [ContinuousLinearMap.det, LinearMap.det_zero, hn.ne']
  set L := fderiv ℂ σ 0 with hL
  have hu : IsUnit (L : V n →ₗ[ℂ] V n) :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hbij : Function.Bijective (L : V n →ₗ[ℂ] V n) := (Module.End.isUnit_iff _).mp hu
  let e : V n ≃L[ℂ] V n := (LinearEquiv.ofBijective (L : V n →ₗ[ℂ] V n) hbij).toContinuousLinearEquiv
  set K : ℝ := ‖(e.symm : V n →L[ℂ] V n)‖ + 1 with hKdef
  have hK : 0 < K := by positivity
  have hle : ∀ z, ‖z‖ ≤ K * ‖L z‖ := by
    intro z
    have h1 : (e.symm : V n →L[ℂ] V n) (L z) = z := by
      have h2 : e z = L z := rfl
      rw [← h2, ContinuousLinearEquiv.coe_coe, e.symm_apply_apply]
    calc ‖z‖ = ‖(e.symm : V n →L[ℂ] V n) (L z)‖ := by rw [h1]
      _ ≤ ‖(e.symm : V n →L[ℂ] V n)‖ * ‖L z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖L z‖ := by gcongr; linarith
  have hc0 : (0 : ℝ) < 1 / (2 * K) := by positivity
  have hcK : 1 / (2 * K) * K = 1 / 2 := by field_simp
  refine ⟨1 / (2 * K), hc0, ?_⟩
  have ho := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hdiff.hasFDerivAt).def hc0
  filter_upwards [ho] with z hz
  simp only [zero_add, h0, sub_zero] at hz
  have h3 : ‖L z‖ ≤ ‖σ z‖ + ‖σ z - L z‖ := by
    have h4 := norm_sub_le (σ z) (σ z - L z)
    simpa using h4
  have h4 : 1 / (2 * K) * ‖z‖ ≤ 1 / (2 * K) * (K * ‖L z‖) := mul_le_mul_of_nonneg_left (hle z) hc0.le
  have h5 : 1 / (2 * K) * (K * ‖L z‖) = ‖L z‖ / 2 := by rw [← mul_assoc, hcK]; ring
  linarith

/- English proof (translation)
Establish `hmv : ¬ (∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ‖y‖ ^ (-2 * (n : ℝ)) < ⊤)` using `fun h => lt_irrefl (n : ℝ) ((ReciprocityTheory.L2DbarEstimates.mvInt n hn (n : ℝ)).mp h)`. Assume the negation of the conclusion as `hfin`. Apply `hmv` to reduce the goal to its premises. Establish `: Nonempty (Fin n)` using `⟨⟨0, hn⟩⟩`. Establish `hne : ∀ᵐ y ∂(volume : Measure (V n)), y ≠ 0`.

Establish `: (volume : Measure (V n)) {0} = 0` using `measure_singleton 0`. Conclude with `measure_eq_zero_iff_ae_notMem.mp this`. Establish `hp : -2 * (n : ℝ) ≤ 0` using `by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith`. Establish `h1 : ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ‖y‖ ^ (-2 * (n : ℝ)) = ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal (‖y‖ ^ (-2 * (n : ℝ)))`. Use `lintegral_congr_ae ((ae_restrict_of_ae hne).mono fun y hy => ?_)` and prove the remaining obligations.

Conclude with `ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hy)`. Establish `h2 : ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal (‖y‖ ^ (-2 * (n : ℝ))) ≤ (∫⁻ y in ball (0 : V n) δ, ENNReal.ofReal (‖y‖ ^ (-2 * (n : ℝ)))) + ∫⁻ y in ball (0 : V n) 1 \ ball (0 : V n) δ, ENNReal.ofReal (‖y‖ ^ (-2 * (n : ℝ)))`. Establish `hsub : ball (0 : V n) 1 ⊆ ball (0 : V n) δ ∪ (ball (0 : V n) 1 \ ball (0 : V n) δ)`. Introduce `y hy`. Distinguish the cases in `h : y ∈ ball (0 : V n) δ`.

Conclude with `Or.inl h`. Conclude with `Or.inr ⟨hy, h⟩`. Conclude with `(lintegral_mono_set (μ := volume) (f := fun y : V n => ENNReal.ofReal (‖y‖ ^ (-2 * (n : ℝ)))) hsub).trans (lintegral_union_le (μ := volume) (fun y : V n => ENNReal.ofReal (‖y‖ ^ (-2 * (n : ℝ)))) (ball (0 : V n) δ) (ball (0 : V n) 1 \ ball (0 : V n) δ))`. Establish `h3 : ∫⁻ y in ball (0 : V n) 1 \ ball (0 : V n) δ, ENNReal.ofReal (‖y‖ ^ (-2 * (n : ℝ))) < ⊤`. Combine the equalities or inequalities in the displayed calculation.

Use `setLIntegral_mono' (measurableSet_ball.diff measurableSet_ball) fun y hy => ?_` and prove the remaining obligations. Use `ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hδ ?_ hp)` and prove the remaining obligations. Use `hy.2` as an intermediate fact. Rewrite `this` using `[mem_ball, dist_zero_right, not_lt]`. Conclude with `this`.

Use `_ = ENNReal.ofReal (δ ^ (-2 * (n : ℝ))) * volume (ball (0 : V n) 1 \ ball (0 : V n) δ) := setLIntegral_const _ _`. Use `_ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt (measure_mono Set.sdiff_subset) measure_ball_lt_top)`. Rewrite using `[h1]`. Conclude with `lt_of_le_of_lt h2 (ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hfin, h3⟩)`.
-/
theorem crit_div {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ z in ball (0 : V n) δ, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) = ⊤ := by
  have hmv : ¬ (∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ‖y‖ ^ (-2 * (n : ℝ)) < ⊤) :=
    fun h => lt_irrefl (n : ℝ) ((ReciprocityTheory.L2DbarEstimates.mvInt n hn (n : ℝ)).mp h)
  by_contra hfin
  apply hmv
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hne : ∀ᵐ y ∂(volume : Measure (V n)), y ≠ 0 := by
    have : (volume : Measure (V n)) {0} = 0 := measure_singleton 0
    exact measure_eq_zero_iff_ae_notMem.mp this
  have hp : -2 * (n : ℝ) ≤ 0 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have h1 : ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ‖y‖ ^ (-2 * (n : ℝ)) =
      ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal (‖y‖ ^ (-2 * (n : ℝ))) := by
    refine lintegral_congr_ae ((ae_restrict_of_ae hne).mono fun y hy => ?_)
    exact ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hy)
  have h2 : ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal (‖y‖ ^ (-2 * (n : ℝ))) ≤
      (∫⁻ y in ball (0 : V n) δ, ENNReal.ofReal (‖y‖ ^ (-2 * (n : ℝ)))) +
        ∫⁻ y in ball (0 : V n) 1 \ ball (0 : V n) δ, ENNReal.ofReal (‖y‖ ^ (-2 * (n : ℝ))) := by
    have hsub : ball (0 : V n) 1 ⊆ ball (0 : V n) δ ∪ (ball (0 : V n) 1 \ ball (0 : V n) δ) := by
      intro y hy
      by_cases h : y ∈ ball (0 : V n) δ
      · exact Or.inl h
      · exact Or.inr ⟨hy, h⟩
    exact (lintegral_mono_set (μ := volume) (f := fun y : V n => ENNReal.ofReal (‖y‖ ^ (-2 * (n : ℝ)))) hsub).trans
      (lintegral_union_le (μ := volume) (fun y : V n => ENNReal.ofReal (‖y‖ ^ (-2 * (n : ℝ))))
        (ball (0 : V n) δ) (ball (0 : V n) 1 \ ball (0 : V n) δ))
  have h3 : ∫⁻ y in ball (0 : V n) 1 \ ball (0 : V n) δ, ENNReal.ofReal (‖y‖ ^ (-2 * (n : ℝ))) < ⊤ := by
    calc ∫⁻ y in ball (0 : V n) 1 \ ball (0 : V n) δ, ENNReal.ofReal (‖y‖ ^ (-2 * (n : ℝ)))
        ≤ ∫⁻ y in ball (0 : V n) 1 \ ball (0 : V n) δ, ENNReal.ofReal (δ ^ (-2 * (n : ℝ))) := by
          refine setLIntegral_mono' (measurableSet_ball.diff measurableSet_ball) fun y hy => ?_
          refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hδ ?_ hp)
          have := hy.2
          rw [mem_ball, dist_zero_right, not_lt] at this
          exact this
      _ = ENNReal.ofReal (δ ^ (-2 * (n : ℝ))) * volume (ball (0 : V n) 1 \ ball (0 : V n) δ) :=
          setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lt_of_le_of_lt (measure_mono Set.sdiff_subset) measure_ball_lt_top)
  rw [h1]
  exact lt_of_le_of_lt h2 (ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hfin, h3⟩)

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show mat x1 τ * mat (nmat X 0) τ = x1 τ`. Establish `h1 : mat (nmat X 0) τ = 1`. Use extensionality with `a b`. Simplify using `only [mat, Matrix.of_apply, nmat, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; subst_vars; exact lt_irrefl _ ‹_›) | simp_all`. Rewrite using `[h1, Matrix.mul_one]`. Both sides reduce to the same expression.
-/
theorem cpt_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x1 : Frame X.Ψ r) : cpt X x1 0 = x1 := by
  funext τ
  show mat x1 τ * mat (nmat X 0) τ = x1 τ
  have h1 : mat (nmat X 0) τ = 1 := by
    ext a b
    simp only [mat, Matrix.of_apply, nmat, Matrix.one_apply]
    split_ifs <;> first | rfl | (exfalso; subst_vars; exact lt_irrefl _ ‹_›) | simp_all
  rw [h1, Matrix.mul_one]
  rfl

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
  Filter ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Introduce `r X x1 hn _ _ u w0 s ρ hρ hu hs _ _ hs0 hdet hint`. Assume the negation of the conclusion as `hne`. Establish `hb : ball (0 : V (nd X)) ρ ∈ 𝓝 (0 : V (nd X))` using `ball_mem_nhds 0 hρ`. Use `set a := ‖u x1‖ with ha`. Establish `ha0 : 0 < a` using `norm_pos_iff.mpr hne`.

Establish `ev1 : ∀ᶠ z in 𝓝 (0 : V (nd X)), a / 2 < ‖u (cpt X x1 z)‖`. Establish `hc : ContinuousAt (fun z => u (cpt X x1 z)) 0` using `hu.continuousOn.continuousAt hb`. Establish `h0 : ‖u (cpt X x1 0)‖ = a` using `by rw [cpt_zero]`. Conclude with `hc.norm.eventually (Ioi_mem_nhds (by show a / 2 < ‖u (cpt X x1 0)‖; rw [h0]; linarith))`. Use `set σ : V (nd X) → V (nd X) := fun z => WithLp.toLp 2 fun k => s k (cpt X x1 z) / w0 (cpt X x1 z) with hσ`.

Establish `hσ0 : σ 0 = 0`. Simplify using `[hσ, cpt_zero, hs0]`. Both sides reduce to the same expression. Take `⟨c, hc, ev2⟩` from `lower_of_det hn hσ0 hdet`. Establish `hsk : ∀ k, ∃ C : ℝ, ∀ᶠ z in 𝓝 (0 : V (nd X)), ‖s k (cpt X x1 z)‖ ≤ C * ‖z‖` using `fun k => bigO_of_diff ((hs k).differentiableAt hb) (by rw [cpt_zero, hs0])`.

Use `choose C hC using hsk`. Take `⟨δ0, hδ0, hall⟩` from `Metric.eventually_nhds_iff.mp (ev1.and (ev2.and ((eventually_all.mpr hC).and (Filter.eventually_of_mem hb fun z hz => hz))))`. Use `set B : ℝ := ∑ k, C k ^ 2 + 1 with hB`. Establish `hB0 : 0 < B` using `by positivity`. Use `set K : ℝ := (a / 2) ^ 2 * B ^ (-(nd X : ℝ)) with hK`.

Establish `hK0 : 0 < K` using `by positivity`. Establish `hp : -(nd X : ℝ) ≤ 0` using `by have : (0 : ℝ) ≤ (nd X : ℝ) := Nat.cast_nonneg _; linarith`. Establish `hpt : ∀ z ∈ ball (0 : V (nd X)) δ0, z ≠ 0 → ENNReal.ofReal K * ENNReal.ofReal (‖z‖ ^ (-2 * (nd X : ℝ))) ≤ ENNReal.ofReal (‖u (cpt X x1 z)‖ ^ 2 * (∑ k, ‖s k (cpt X x1 z)‖ ^ 2) ^ (-(nd X : ℝ)))`. Introduce `z hz hz0`. Take `⟨h1, h2, h3, -⟩` from `hall (by simpa using hz)`.

Establish `hzpos : 0 < ‖z‖` using `norm_pos_iff.mpr hz0`. Use `set S := ∑ k, ‖s k (cpt X x1 z)‖ ^ 2 with hS`. Establish `hSle : S ≤ B * ‖z‖ ^ 2`. Establish `: S ≤ ∑ k, (C k * ‖z‖) ^ 2` using `Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (h3 k) 2`. Combine the equalities or inequalities in the displayed calculation.

Establish `hSpos : 0 < S`. Establish `hσz : σ z ≠ 0`. Introduce `h0`. Use `h2` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`.

Use the polynomial consequences of the given equalities and inequalities. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, s k (cpt X x1 z) / w0 (cpt X x1 z) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hσz` to reduce the goal to its premises.

Simplify using `only [hσ, hcon]`. Both sides reduce to the same expression. Establish `hsk0 : s k (cpt X x1 z) ≠ 0` using `fun h => hk (by rw [h, zero_div])`. Conclude with `lt_of_lt_of_le (by positivity : 0 < ‖s k (cpt X x1 z)‖ ^ 2) (Finset.single_le_sum (f := fun k => ‖s k (cpt X x1 z)‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ k))`. Rewrite using `[← ENNReal.ofReal_mul hK0.le]`.

Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `hSp : (B * ‖z‖ ^ 2) ^ (-(nd X : ℝ)) ≤ S ^ (-(nd X : ℝ))` using `Real.rpow_le_rpow_of_nonpos hSpos hSle hp`. Establish `hexp : (B * ‖z‖ ^ 2) ^ (-(nd X : ℝ)) = B ^ (-(nd X : ℝ)) * ‖z‖ ^ (-2 * (nd X : ℝ))`. Rewrite using `[Real.mul_rpow hB0.le (by positivity), ← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]`. Put the polynomial expressions in normal form.

Establish `hu2 : (a / 2) ^ 2 ≤ ‖u (cpt X x1 z)‖ ^ 2` using `pow_le_pow_left₀ (by positivity) h1.le 2`. Combine the equalities or inequalities in the displayed calculation. Establish `hne0 : ∀ᵐ z ∂(volume : Measure (V (nd X))), z ≠ 0`. Establish `: Nonempty (Fin (nd X))` using `⟨⟨0, hn⟩⟩`. Conclude with `measure_eq_zero_iff_ae_notMem.mp (measure_singleton 0)`.

Establish `hsub : ball (0 : V (nd X)) δ0 ⊆ ball (0 : V (nd X)) ρ` using `fun z hz => (hall (by simpa using hz)).2.2.2`. Establish `hlow : ENNReal.ofReal K * ∫⁻ z in ball (0 : V (nd X)) δ0, ENNReal.ofReal (‖z‖ ^ (-2 * (nd X : ℝ))) ≤ ∫⁻ z in ball (0 : V (nd X)) ρ, ENNReal.ofReal (‖u (cpt X x1 z)‖ ^ 2 * (∑ k, ‖s k (cpt X x1 z)‖ ^ 2) ^ (-(nd X : ℝ)))`. Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `le_trans ?_ (lintegral_mono_set hsub)` and prove the remaining obligations. Use `lintegral_mono_ae ?_` and prove the remaining obligations.

Use `filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne0] with z hz hz0`. Conclude with `hpt z hz hz0`. Rewrite `hlow` using `[crit_div hn hδ0, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hK0).ne']`. Conclude with `absurd (lt_of_le_of_lt hlow hint) (lt_irrefl _)`.
-/
theorem vanishAtS_holds : VanishAtSStatement (E := E) := by
  intro r X x1 hn _ _ u w0 s ρ hρ hu hs _ _ hs0 hdet hint
  by_contra hne
  have hb : ball (0 : V (nd X)) ρ ∈ 𝓝 (0 : V (nd X)) := ball_mem_nhds 0 hρ
  set a := ‖u x1‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr hne

  have ev1 : ∀ᶠ z in 𝓝 (0 : V (nd X)), a / 2 < ‖u (cpt X x1 z)‖ := by
    have hc : ContinuousAt (fun z => u (cpt X x1 z)) 0 := hu.continuousOn.continuousAt hb
    have h0 : ‖u (cpt X x1 0)‖ = a := by rw [cpt_zero]
    exact hc.norm.eventually (Ioi_mem_nhds (by show a / 2 < ‖u (cpt X x1 0)‖; rw [h0]; linarith))

  set σ : V (nd X) → V (nd X) := fun z => WithLp.toLp 2 fun k => s k (cpt X x1 z) / w0 (cpt X x1 z) with hσ
  have hσ0 : σ 0 = 0 := by
    simp [hσ, cpt_zero, hs0]
    rfl
  obtain ⟨c, hc, ev2⟩ := lower_of_det hn hσ0 hdet

  have hsk : ∀ k, ∃ C : ℝ, ∀ᶠ z in 𝓝 (0 : V (nd X)), ‖s k (cpt X x1 z)‖ ≤ C * ‖z‖ := fun k =>
    bigO_of_diff ((hs k).differentiableAt hb) (by rw [cpt_zero, hs0])
  choose C hC using hsk
  obtain ⟨δ0, hδ0, hall⟩ := Metric.eventually_nhds_iff.mp
    (ev1.and (ev2.and ((eventually_all.mpr hC).and (Filter.eventually_of_mem hb fun z hz => hz))))
  set B : ℝ := ∑ k, C k ^ 2 + 1 with hB
  have hB0 : 0 < B := by positivity
  set K : ℝ := (a / 2) ^ 2 * B ^ (-(nd X : ℝ)) with hK
  have hK0 : 0 < K := by positivity
  have hp : -(nd X : ℝ) ≤ 0 := by have : (0 : ℝ) ≤ (nd X : ℝ) := Nat.cast_nonneg _; linarith
  have hpt : ∀ z ∈ ball (0 : V (nd X)) δ0, z ≠ 0 →
      ENNReal.ofReal K * ENNReal.ofReal (‖z‖ ^ (-2 * (nd X : ℝ))) ≤
        ENNReal.ofReal (‖u (cpt X x1 z)‖ ^ 2 * (∑ k, ‖s k (cpt X x1 z)‖ ^ 2) ^ (-(nd X : ℝ))) := by
    intro z hz hz0
    obtain ⟨h1, h2, h3, -⟩ := hall (by simpa using hz)
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    set S := ∑ k, ‖s k (cpt X x1 z)‖ ^ 2 with hS
    have hSle : S ≤ B * ‖z‖ ^ 2 := by
      have : S ≤ ∑ k, (C k * ‖z‖) ^ 2 :=
        Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (h3 k) 2
      calc S ≤ ∑ k, (C k * ‖z‖) ^ 2 := this
        _ = (∑ k, C k ^ 2) * ‖z‖ ^ 2 := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
        _ ≤ B * ‖z‖ ^ 2 := by rw [hB]; nlinarith [sq_nonneg ‖z‖]
    have hSpos : 0 < S := by
      have hσz : σ z ≠ 0 := by
        intro h0
        have := h2
        rw [h0, norm_zero] at this
        nlinarith
      obtain ⟨k, hk⟩ : ∃ k, s k (cpt X x1 z) / w0 (cpt X x1 z) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hσz
        simp only [hσ, hcon]
        rfl
      have hsk0 : s k (cpt X x1 z) ≠ 0 := fun h => hk (by rw [h, zero_div])
      exact lt_of_lt_of_le (by positivity : 0 < ‖s k (cpt X x1 z)‖ ^ 2)
        (Finset.single_le_sum (f := fun k => ‖s k (cpt X x1 z)‖ ^ 2) (fun k _ => by positivity)
          (Finset.mem_univ k))
    rw [← ENNReal.ofReal_mul hK0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hSp : (B * ‖z‖ ^ 2) ^ (-(nd X : ℝ)) ≤ S ^ (-(nd X : ℝ)) := Real.rpow_le_rpow_of_nonpos hSpos hSle hp
    have hexp : (B * ‖z‖ ^ 2) ^ (-(nd X : ℝ)) = B ^ (-(nd X : ℝ)) * ‖z‖ ^ (-2 * (nd X : ℝ)) := by
      rw [Real.mul_rpow hB0.le (by positivity), ← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
      ring_nf
    have hu2 : (a / 2) ^ 2 ≤ ‖u (cpt X x1 z)‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1.le 2
    calc K * ‖z‖ ^ (-2 * (nd X : ℝ)) = (a / 2) ^ 2 * (B * ‖z‖ ^ 2) ^ (-(nd X : ℝ)) := by rw [hexp, hK]; ring
      _ ≤ ‖u (cpt X x1 z)‖ ^ 2 * S ^ (-(nd X : ℝ)) :=
        mul_le_mul hu2 hSp (by positivity) (by positivity)
  have hne0 : ∀ᵐ z ∂(volume : Measure (V (nd X))), z ≠ 0 := by
    have : Nonempty (Fin (nd X)) := ⟨⟨0, hn⟩⟩
    exact measure_eq_zero_iff_ae_notMem.mp (measure_singleton 0)
  have hsub : ball (0 : V (nd X)) δ0 ⊆ ball (0 : V (nd X)) ρ := fun z hz =>
    (hall (by simpa using hz)).2.2.2
  have hlow : ENNReal.ofReal K * ∫⁻ z in ball (0 : V (nd X)) δ0, ENNReal.ofReal (‖z‖ ^ (-2 * (nd X : ℝ))) ≤
      ∫⁻ z in ball (0 : V (nd X)) ρ, ENNReal.ofReal (‖u (cpt X x1 z)‖ ^ 2 *
        (∑ k, ‖s k (cpt X x1 z)‖ ^ 2) ^ (-(nd X : ℝ))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans ?_ (lintegral_mono_set hsub)
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne0] with z hz hz0
    exact hpt z hz hz0
  rw [crit_div hn hδ0, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hK0).ne'] at hlow
  exact absurd (lt_of_le_of_lt hlow hint) (lt_irrefl _)

end ReciprocityTheory.ChartRestriction.G.AR.Up
