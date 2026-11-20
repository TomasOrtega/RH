import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bNormHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bExpHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.EmbeddingHermitianPairs

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom

namespace GlobalTheory.CuspStep

/- English proof (translation)
Use `PhragmenLindelof.right_half_plane_of_bounded_on_real (f := g) ?_ ⟨0, by norm_num, 0, ?_⟩ ?_ hC (by simp)` and prove the remaining obligations. Use `DifferentiableOn.diffContOnCl ?_` and prove the remaining obligations. Rewrite using `[Complex.closure_setOf_lt_re]`. Conclude with `hd`. Use `Asymptotics.IsBigO.of_bound M ?_` and prove the remaining obligations.

Use `Filter.Eventually.filter_mono inf_le_right ?_` and prove the remaining obligations. Rewrite using `[Filter.eventually_principal]`. Introduce `z hz`. Simplify using `using hM z (le_of_lt hz)`. Use `⟨M, ?_⟩` and prove the remaining obligations.

Rewrite using `[Filter.eventually_map]`. Use `filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with y hy`. Conclude with `hM y (by simpa using hy)`.
-/
theorem half_plane_bound {g : ℂ → ℂ} {M C : ℝ} (hd : DifferentiableOn ℂ g {z | 0 ≤ z.re})
    (hM : ∀ z : ℂ, 0 ≤ z.re → ‖g z‖ ≤ M) (hC : ∀ y : ℝ, ‖g (y * I)‖ ≤ C) : ‖g 1‖ ≤ C := by
  refine PhragmenLindelof.right_half_plane_of_bounded_on_real (f := g) ?_ ⟨0, by norm_num, 0, ?_⟩ ?_ hC (by simp)
  · refine DifferentiableOn.diffContOnCl ?_
    rw [Complex.closure_setOf_lt_re]
    exact hd
  · refine Asymptotics.IsBigO.of_bound M ?_
    refine Filter.Eventually.filter_mono inf_le_right ?_
    rw [Filter.eventually_principal]
    intro z hz
    simpa using hM z (le_of_lt hz)
  · refine ⟨M, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with y hy
    exact hM y (by simpa using hy)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Use `differentiable_pi.mpr fun τ => differentiable_pi.mpr fun i => differentiable_pi.mpr fun j => ?_` and prove the remaining obligations. Simplify using `only [Data.flow, Data.flowMat, Matrix.mul_apply, Matrix.of_apply]`. Use `fun_prop`.
-/
theorem differentiable_flow (ξ : Fin r → E) (a : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    Differentiable ℂ (fun z : ℂ => X.flow ξ (fun τ => z * a τ) x) := by
  refine differentiable_pi.mpr fun τ => differentiable_pi.mpr fun i => differentiable_pi.mpr fun j => ?_
  simp only [Data.flow, Data.flowMat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

/- English proof (translation)
Establish `hd : X.flow ξ s x ∈ X.dom` using `FjCauchy.flow_mem_dom X hξ hx s fun τ => by rw [hs, add_zero]; exact FjCauchy.tt_pos X hξ hx τ`. Establish `h` using `m3bNorm_holds r X _ (FjCauchy.isIsoV_embV X hξ) la x hx s hd`. Simplify using `only [hs, zero_div, add_zero, inv_one, min_self, max_self, Real.one_rpow, Finset.prod_const_one] at h`. Establish `h1 : X.nfac la x / X.nfac la (X.flow ξ s x) = 1` using `le_antisymm h.2 h.1`. Establish `hn` using `FlowCoefficientBounds.nfac_pos X hd la`.

Rewrite `h1` using `[div_eq_one_iff_eq hn.ne']`. Conclude with `h1.symm`.
-/
theorem nfac_flow_real (la : Wt X.Ψ r) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (s : X.Ψ → ℂ) (hs : ∀ τ, (s τ).im = 0) : X.nfac la (X.flow ξ s x) = X.nfac la x := by
  have hd : X.flow ξ s x ∈ X.dom :=
    FjCauchy.flow_mem_dom X hξ hx s fun τ => by rw [hs, add_zero]; exact FjCauchy.tt_pos X hξ hx τ
  have h := m3bNorm_holds r X _ (FjCauchy.isIsoV_embV X hξ) la x hx s hd
  simp only [hs, zero_div, add_zero, inv_one, min_self, max_self, Real.one_rpow, Finset.prod_const_one] at h
  have h1 : X.nfac la x / X.nfac la (X.flow ξ s x) = 1 := le_antisymm h.2 h.1
  have hn := FlowCoefficientBounds.nfac_pos X hd la
  rw [div_eq_one_iff_eq hn.ne'] at h1
  exact h1.symm

/- English proof (translation)
Establish `hd : X.flow ξ s x ∈ X.dom` using `FjCauchy.flow_mem_dom X hξ hx s fun τ => add_pos_of_pos_of_nonneg (FjCauchy.tt_pos X hξ hx τ) (hs τ)`. Establish `h0` using `m3bExp_holds r X la P hP ξ hξ x hx 0 (by rw [EmbeddingHermitianPairs.flow_zero]; exact hx)`. Simplify using `only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.exp_zero, mul_one] at h0`. Establish `hsum : Summable fun ν : X.Ψ → ℝ => ‖X.fj la ξ ν P x‖` using `summable_norm_iff.mpr h0.summable`. Establish `h1` using `m3bExp_holds r X la P hP ξ hξ x hx s hd`.

Use `h1.norm_le_of_bounded hsum.hasSum fun ν => ?_` and prove the remaining obligations. Distinguish the cases in `hz : X.fj la ξ ν P x = 0`. Simplify using `[hz]`. Establish `hν` using `hF ξ hξ ν x hx hz`. Rewrite using `[norm_mul]`.

Use `mul_le_of_le_one_right (norm_nonneg _) ?_` and prove the remaining obligations. Rewrite using `[Complex.norm_exp, Real.exp_le_one_iff]`. Establish `hsn : 0 ≤ ∑ τ, ν τ * (s τ).im` using `Finset.sum_nonneg fun τ _ => mul_nonneg (hν τ) (hs τ)`. Establish `: (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ).re = -(4 * Real.pi * ∑ τ, ν τ * (s τ).im)`. Simplify using `[Complex.mul_re, Complex.mul_im, Complex.im_sum]`.

Rewrite using `[this]`. Use `Real.pi_pos` as an intermediate fact. Establish `: 0 ≤ 4 * Real.pi * ∑ τ, ν τ * (s τ).im` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_flow_le {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) (hF : FreqNonneg X la P)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hs : ∀ τ, 0 ≤ (s τ).im) :
    ‖P (X.flow ξ s x)‖ ≤ ∑' ν : X.Ψ → ℝ, ‖X.fj la ξ ν P x‖ := by
  have hd : X.flow ξ s x ∈ X.dom :=
    FjCauchy.flow_mem_dom X hξ hx s fun τ => add_pos_of_pos_of_nonneg (FjCauchy.tt_pos X hξ hx τ) (hs τ)
  have h0 := m3bExp_holds r X la P hP ξ hξ x hx 0 (by rw [EmbeddingHermitianPairs.flow_zero]; exact hx)
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.exp_zero, mul_one] at h0
  have hsum : Summable fun ν : X.Ψ → ℝ => ‖X.fj la ξ ν P x‖ := summable_norm_iff.mpr h0.summable
  have h1 := m3bExp_holds r X la P hP ξ hξ x hx s hd
  refine h1.norm_le_of_bounded hsum.hasSum fun ν => ?_
  by_cases hz : X.fj la ξ ν P x = 0
  · simp [hz]
  · have hν := hF ξ hξ ν x hx hz
    rw [norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    have hsn : 0 ≤ ∑ τ, ν τ * (s τ).im := Finset.sum_nonneg fun τ _ => mul_nonneg (hν τ) (hs τ)
    have : (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ).re = -(4 * Real.pi * ∑ τ, ν τ * (s τ).im) := by
      simp [Complex.mul_re, Complex.mul_im, Complex.im_sum]
    rw [this]
    have := Real.pi_pos
    have : 0 ≤ 4 * Real.pi * ∑ τ, ν τ * (s τ).im := by positivity
    linarith

/- English proof (translation)
Introduce `ξ hξ x hx q hq B hB`. Establish `ht` using `FjCauchy.tt_pos X hξ hx`. Use `set b : X.Ψ → ℂ := fun τ => I * (((q τ - 1) * X.tt ξ x τ : ℝ) : ℂ) with hb`. Establish `hbim : ∀ τ, (b τ).im = (q τ - 1) * X.tt ξ x τ` using `fun τ => by`. Simplify using `only [hb, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hbre : ∀ τ, (b τ).re = 0` using `fun τ => by`. Simplify using `only [hb, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]`. Expand and normalize the polynomial expressions, which then agree. Establish `hbn : ∀ τ, (b τ).im ≤ 0` using `fun τ => by`.

Rewrite using `[hbim]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith [(hq τ).2]) (ht τ).le`. Establish `hx' : X.flow ξ b x ∈ X.dom` using `FjCauchy.flow_mem_dom X hξ hx b fun τ => by`. Rewrite using `[hbim]`. Use polynomial arithmetic with `[mul_pos (hq τ).1 (ht τ)]`. Use `set x' := X.flow ξ b x with hx'def`.

Establish `hn'` using `FlowCoefficientBounds.nfac_pos X hx' la`. Establish `hn` using `FlowCoefficientBounds.nfac_pos X hx la`. Establish `him : ∀ z : ℂ, 0 ≤ z.re → ∀ τ, 0 ≤ (z * -b τ).im` using `fun z hz τ => by`. Simplify using `only [Complex.mul_im, Complex.neg_im, Complex.neg_re, hbre, neg_zero, mul_zero, add_zero]`. Conclude with `mul_nonneg hz (by linarith [hbn τ])`.

Establish `hreal : ∀ y : ℝ, ‖P (X.flow ξ (fun τ => (y * I) * -b τ) x')‖ ≤ B / X.nfac la x'` using `fun y => by`. Establish `hs : ∀ τ, ((y * I : ℂ) * -b τ).im = 0` using `fun τ => by simp [hbre]`. Rewrite using `[le_div_iff₀ hn', ← nfac_flow_real X la hξ hx' _ hs]`. Establish `h` using `hB fun τ => ((y * I : ℂ) * -b τ).re`. Establish `he : X.flow ξ (fun τ => (y * I) * -b τ) x' = X.flow ξ (fun τ => (((y * I : ℂ) * -b τ).re : ℂ) + b τ) x`.

Rewrite using `[hx'def, EmbeddingHermitianPairs.flow_flow X hξ.2.1]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Simplify using `only [Pi.add_apply]`. Use `congr 1`.

Conclude with `Complex.ext (by simp) (by rw [hs]; simp)`. Rewrite using `[he]`. Conclude with `h`. Establish `key` using `half_plane_bound (g := fun z => P (X.flow ξ (fun τ => z * -b τ) x')) (hP.1.comp (differentiable_flow X ξ (fun τ => -b τ) x').differentiableOn fun z hz => FjCauchy.flow_mem_dom X hξ hx' _ fun τ => add_pos_of_pos_of_nonneg (FjCauchy.tt_pos X hξ hx' τ) (him z hz τ)) (fun z hz => nor …`. Establish `he : X.flow ξ (fun τ => 1 * -b τ) x' = x`.

Rewrite using `[hx'def, EmbeddingHermitianPairs.flow_flow X hξ.2.1]`. Establish `: ((fun τ => 1 * -b τ) + b) = 0` using `by funext τ; simp`. Rewrite using `[this, EmbeddingHermitianPairs.flow_zero]`. Simplify using `only [he] at key`. Establish `hB0 : 0 ≤ B`.

Use `(norm_nonneg _).trans key` as an intermediate fact. Conclude with `(div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hn'))`. Establish `hr` using `(m3bNorm_holds r X _ (FjCauchy.isIsoV_embV X hξ) la x hx b hx').2`. Establish `hr2 : X.nfac la x / X.nfac la x' ≤ ∏ τ, q τ ^ (-w)`. Use `le_trans hr (Finset.prod_le_prod (fun τ _ => ?_) fun τ _ => ?_)` and prove the remaining obligations.

Use `all_goals`. Establish `hqq : 1 + (b τ).im / X.ttV (X.embV ξ) x τ = q τ`. Express the relevant statement in the definitionally equal form `1 + (b τ).im / X.tt ξ x τ = q τ`. Rewrite using `[hbim, mul_div_assoc, div_self (ht τ).ne']`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1 : 1 ≤ (q τ)⁻¹` using `(one_le_inv₀ (hq τ).1).mpr (hq τ).2`. Simplify using `only [hqq, max_eq_right ((hq τ).2.trans h1)]`. Check the signs of the components of the expression. Rewrite using `[Real.rpow_neg (hq τ).1.le, ← Real.inv_rpow (hq τ).1.le]`. Conclude with `Real.rpow_le_rpow_of_exponent_le h1 (hw τ)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem stepBound (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (w : ℝ) (hP : X.IsSec la P) (hF : FreqNonneg X la P)
    (hw : ∀ τ, X.spread la τ / 2 ≤ w) : StepBound X w (X.pnorm la P) := by
  intro ξ hξ x hx q hq B hB
  have ht := FjCauchy.tt_pos X hξ hx
  set b : X.Ψ → ℂ := fun τ => I * (((q τ - 1) * X.tt ξ x τ : ℝ) : ℂ) with hb
  have hbim : ∀ τ, (b τ).im = (q τ - 1) * X.tt ξ x τ := fun τ => by
    simp only [hb, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hbre : ∀ τ, (b τ).re = 0 := fun τ => by
    simp only [hb, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hbn : ∀ τ, (b τ).im ≤ 0 := fun τ => by
    rw [hbim]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith [(hq τ).2]) (ht τ).le
  have hx' : X.flow ξ b x ∈ X.dom := FjCauchy.flow_mem_dom X hξ hx b fun τ => by
    rw [hbim]; nlinarith [mul_pos (hq τ).1 (ht τ)]
  set x' := X.flow ξ b x with hx'def
  have hn' := FlowCoefficientBounds.nfac_pos X hx' la
  have hn := FlowCoefficientBounds.nfac_pos X hx la
  have him : ∀ z : ℂ, 0 ≤ z.re → ∀ τ, 0 ≤ (z * -b τ).im := fun z hz τ => by
    simp only [Complex.mul_im, Complex.neg_im, Complex.neg_re, hbre, neg_zero, mul_zero, add_zero]
    exact mul_nonneg hz (by linarith [hbn τ])
  have hreal : ∀ y : ℝ, ‖P (X.flow ξ (fun τ => (y * I) * -b τ) x')‖ ≤ B / X.nfac la x' := fun y => by
    have hs : ∀ τ, ((y * I : ℂ) * -b τ).im = 0 := fun τ => by simp [hbre]
    rw [le_div_iff₀ hn', ← nfac_flow_real X la hξ hx' _ hs]
    have h := hB fun τ => ((y * I : ℂ) * -b τ).re
    have he : X.flow ξ (fun τ => (y * I) * -b τ) x' =
        X.flow ξ (fun τ => (((y * I : ℂ) * -b τ).re : ℂ) + b τ) x := by
      rw [hx'def, EmbeddingHermitianPairs.flow_flow X hξ.2.1]
      congr 1
      funext τ
      simp only [Pi.add_apply]
      congr 1
      exact Complex.ext (by simp) (by rw [hs]; simp)
    rw [he]
    exact h
  have key := half_plane_bound (g := fun z => P (X.flow ξ (fun τ => z * -b τ) x'))
    (hP.1.comp (differentiable_flow X ξ (fun τ => -b τ) x').differentiableOn fun z hz =>
      FjCauchy.flow_mem_dom X hξ hx' _ fun τ =>
        add_pos_of_pos_of_nonneg (FjCauchy.tt_pos X hξ hx' τ) (him z hz τ))
    (fun z hz => norm_flow_le X hP hF hξ hx' _ (him z hz)) hreal
  have he : X.flow ξ (fun τ => 1 * -b τ) x' = x := by
    rw [hx'def, EmbeddingHermitianPairs.flow_flow X hξ.2.1]
    have : ((fun τ => 1 * -b τ) + b) = 0 := by funext τ; simp
    rw [this, EmbeddingHermitianPairs.flow_zero]
  simp only [he] at key
  have hB0 : 0 ≤ B := by
    have := (norm_nonneg _).trans key
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hn'))
  have hr := (m3bNorm_holds r X _ (FjCauchy.isIsoV_embV X hξ) la x hx b hx').2
  have hr2 : X.nfac la x / X.nfac la x' ≤ ∏ τ, q τ ^ (-w) := by
    refine le_trans hr (Finset.prod_le_prod (fun τ _ => ?_) fun τ _ => ?_)
    all_goals
      have hqq : 1 + (b τ).im / X.ttV (X.embV ξ) x τ = q τ := by
        change 1 + (b τ).im / X.tt ξ x τ = q τ
        rw [hbim, mul_div_assoc, div_self (ht τ).ne']; ring
      have h1 : 1 ≤ (q τ)⁻¹ := (one_le_inv₀ (hq τ).1).mpr (hq τ).2
      simp only [hqq, max_eq_right ((hq τ).2.trans h1)]
    · positivity
    · rw [Real.rpow_neg (hq τ).1.le, ← Real.inv_rpow (hq τ).1.le]
      exact Real.rpow_le_rpow_of_exponent_le h1 (hw τ)
  calc X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
    _ ≤ B / X.nfac la x' * X.nfac la x := mul_le_mul_of_nonneg_right key hn.le
    _ = B * (X.nfac la x / X.nfac la x') := by ring
    _ ≤ B * ∏ τ, q τ ^ (-w) := mul_le_mul_of_nonneg_left hr2 hB0

end GlobalTheory.CuspStep
