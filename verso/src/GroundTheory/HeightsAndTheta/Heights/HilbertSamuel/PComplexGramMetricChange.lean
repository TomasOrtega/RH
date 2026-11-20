import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexGramMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFSExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMetricPair
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionFormsIndependent
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Asymptotics
open scoped ComplexConjugate Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace ComplexGramMetricChange

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

/- English proof (translation)
Rewrite using `[eval_eq, eval_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Establish `hdeg : s.degree = n`. Assume the negation of the conclusion as `h`. Conclude with `(mem_support_iff.mp hs) (hF.coeff_eq_zero h)`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Establish `h : s.degree = ∑ i ∈ s.support, s i` using `rfl`. Rewrite using `[← hdeg, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_smul_of_homog {ι : Type*} {F : MvPolynomial ι ℂ} {n : ℕ} (hF : F.IsHomogeneous n) (c : ℂ)
    (z : ι → ℂ) : eval (c • z) F = c ^ n * eval z F := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hdeg : s.degree = n := by
    by_contra h
    exact (mem_support_iff.mp hs) (hF.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have h : s.degree = ∑ i ∈ s.support, s i := rfl
  rw [← hdeg, h]
  ring

/- English proof (translation)
Take `⟨i, hi⟩` from `(d.R.mem y y (d.R.mem_U y)).1 ()`. Introduce `h`. Conclude with `hi (congrFun h ⟨(), i⟩)`.
-/
theorem resPt_ne_zero (d : HSMDatum D Ω κ) (y : d.R.X) : resPt d y ≠ 0 := by
  obtain ⟨i, hi⟩ := (d.R.mem y y (d.R.mem_U y)).1 ()
  intro h
  exact hi (congrFun h ⟨(), i⟩)

/- English proof (translation)
Establish `hρ : 0 < m.ρ z` using `m.pos z hz`. Establish `hcn : 0 < ‖c‖` using `norm_pos_iff.2 hc`. Establish `hexp : Real.exp (-(n : ℝ) * (2 * Real.log (m.ρ (c • z)))) = ((‖c‖ * m.ρ z) ^ (2 * n))⁻¹`. Rewrite using `[m.smul, show -(n : ℝ) * (2 * Real.log (‖c‖ * m.ρ z)) = -(((2 * n : ℕ) : ℝ) * Real.log (‖c‖ * m.ρ z)) by push_cast; ring, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (mul_pos hcn hρ)]`. Establish `hcc : c ^ n * conj c ^ n = ((‖c‖ : ℝ) : ℂ) ^ (2 * n)`.

Rewrite using `[← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hexp, eval_smul_of_homog (hb.map _), eval_smul_of_homog (hb'.map _), pairVal]`. Establish `hρc : ((m.ρ z : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hρ.ne'`.

Establish `hcc' : ((‖c‖ : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hcn.ne'`. Simplify using `only [map_mul, map_pow]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(eval z (map (algebraMap ℚ ℂ) b) * conj (eval z (map (algebraMap ℚ ℂ) b')) * ((m.ρ z : ℝ) : ℂ) ^ (2 * n)) * hcc`.
-/
theorem pair_smul (m : ConeMetric ℂ (Ix κ)) {z : Ix κ → ℂ} (hz : z ≠ 0) {c : ℂ} (hc : c ≠ 0) {n : ℕ}
    {b b' : MvPolynomial (Ix κ) ℚ} (hb : b.IsHomogeneous n) (hb' : b'.IsHomogeneous n) :
    eval (c • z) (map (algebraMap ℚ ℂ) b) * conj (eval (c • z) (map (algebraMap ℚ ℂ) b')) *
        ((Real.exp (-(n : ℝ) * (2 * Real.log (m.ρ (c • z)))) : ℝ) : ℂ) = pairVal m n b b' z := by
  have hρ : 0 < m.ρ z := m.pos z hz
  have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hexp : Real.exp (-(n : ℝ) * (2 * Real.log (m.ρ (c • z)))) = ((‖c‖ * m.ρ z) ^ (2 * n))⁻¹ := by
    rw [m.smul, show -(n : ℝ) * (2 * Real.log (‖c‖ * m.ρ z)) = -(((2 * n : ℕ) : ℝ) * Real.log (‖c‖ * m.ρ z)) by
      push_cast; ring, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (mul_pos hcn hρ)]
  have hcc : c ^ n * conj c ^ n = ((‖c‖ : ℝ) : ℂ) ^ (2 * n) := by
    rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
    push_cast
    ring
  rw [hexp, eval_smul_of_homog (hb.map _), eval_smul_of_homog (hb'.map _), pairVal]
  have hρc : ((m.ρ z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  have hcc' : ((‖c‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hcn.ne'
  simp only [map_mul, map_pow]
  push_cast
  field_simp
  linear_combination (eval z (map (algebraMap ℚ ℂ) b) * conj (eval z (map (algebraMap ℚ ℂ) b')) *
    ((m.ρ z : ℝ) : ℂ) ^ (2 * n)) * hcc

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Establish `hx : x ∈ (A.chart (chartIdx A x)).source` using `Classical.choose_spec (A.cover x)`. Use `set j := chartIdx A x`. Establish `hT : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source = (A.chart j).target` using `Set.inter_eq_left.2 fun y hy => (A.chart j).map_target hy`.

Establish `h₁` using `(W₁.smooth j j).continuousOn`. Establish `h₀` using `(W₀.smooth j j).continuousOn`. Rewrite `h₁`, `h₀` using `[hT]`. Establish `hg` using `(h₁.sub h₀).continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hx))`. Use `(hg.comp ((A.chart j).continuousAt hx)).congr ?_` and prove the remaining obligations.

Use `filter_upwards [(A.chart j).open_source.mem_nhds hx] with y hy`. Simplify using `only [Pi.sub_apply, Function.comp_apply, (A.chart j).left_inv hy]`. Conclude with `(Weight.diff_eq W₁ W₀ j hy).symm`.
-/
theorem continuous_diff {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}
    (W₁ W₀ : Weight L) : Continuous (Weight.diff W₁ W₀) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  set j := chartIdx A x
  have hT : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source = (A.chart j).target :=
    Set.inter_eq_left.2 fun y hy => (A.chart j).map_target hy
  have h₁ := (W₁.smooth j j).continuousOn
  have h₀ := (W₀.smooth j j).continuousOn
  rw [hT] at h₁ h₀
  have hg := (h₁.sub h₀).continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hx))
  refine (hg.comp ((A.chart j).continuousAt hx)).congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hx] with y hy
  simp only [Pi.sub_apply, Function.comp_apply, (A.chart j).left_inv hy]
  exact (Weight.diff_eq W₁ W₀ j hy).symm

/- English proof (translation)
Take `⟨D', rfl⟩ : ∃ D', D = D' + 1` from `⟨D - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Take `⟨N, hN⟩` from `exists_nat_ge (|C| * 2 ^ D' / ε)`. Use `filter_upwards [eventually_ge_atTop (max N 1)] with n hn`. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast le_of_max_le_right hn`.

Establish `hnN : (N : ℝ) ≤ n` using `by exact_mod_cast le_of_max_le_left hn`. Establish `hkey : |C| * 2 ^ D' ≤ ε * n`. Use `hN.trans hnN` as an intermediate fact. Rewrite `this` using `[div_le_iff₀ hε]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem eventually_pow_le (C ε : ℝ) (hε : 0 < ε) (hD : 1 ≤ D) :
    ∀ᶠ n : ℕ in atTop, C * ((n : ℝ) + 1) ^ (D - 1) ≤ ε * (n : ℝ) ^ D := by
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨N, hN⟩ := exists_nat_ge (|C| * 2 ^ D' / ε)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
  have hkey : |C| * 2 ^ D' ≤ ε * n := by
    have := hN.trans hnN
    rw [div_le_iff₀ hε] at this
    linarith
  calc C * ((n : ℝ) + 1) ^ D' ≤ |C| * ((n : ℝ) + 1) ^ D' :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 * (n : ℝ)) ^ D' :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) (abs_nonneg C)
    _ = (|C| * 2 ^ D') * (n : ℝ) ^ D' := by rw [mul_pow]; ring
    _ ≤ (ε * n) * (n : ℝ) ^ D' := mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = ε * (n : ℝ) ^ (D' + 1) := by ring

end ComplexGramMetricChange

open ComplexGramMetricChange in

/- English proof (translation)
Introduce `D Ω _ _ κ _ d m₁ P0₁ hs hc hle hp e he`. Take `⟨A, L, W₀, W₁, dV, σ, -, hW₀, hW₁, hμ, hsec, hval, hdens⟩` from `hPair D Ω κ d m₁ P0₁ hs hle hp`. Use `choose c hc0 hσ hφ₀ hφ₁ using hval`. Establish `hex : ∀ n, ∃ q : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n q.2` using `fun n => by`. Take `⟨b, hb⟩` from `exists_isSecBasis d.x n`.

Conclude with `⟨⟨_, b⟩, hb⟩`. Set `p : ℕ → (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ)` to `fun n => (hex n).choose`. Establish `hp' : ∀ n, IsSecBasis d.x n (p n).2` using `fun n => (hex n).choose_spec`. Establish `hhom : ∀ n k, ((p n).2 k).IsHomogeneous n` using `fun n k => by`. Take `⟨f, hf, hfe⟩` from `(hp' n).1 k`.

Rewrite using `[hfe]`. Conclude with `hf.map _`. Set `v : ∀ n, Fin (p n).1 → Fin A.n → d.R.X → ℂ` to `fun n k => σ n ((p n).2 k)`. Establish `hli : ∀ n, LinearIndependent ℂ (v n)`. Introduce `n`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `h0 : g = 0` using `hInd D Ω κ d n _ (p n).2 (hp' n) g fun y => by`. Establish `h` using `congrFun (congrFun hg (chartIdx A y)) y`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v, hσ y n _ (hhom n _), eval_smul_of_homog ((hhom n _).map _)] at h`.

Establish `hcn : c y ^ n ≠ 0` using `pow_ne_zero _ (hc0 y)`. Apply `(mul_right_inj' hcn).1` to reduce the goal to its premises. Rewrite using `[mul_zero, Finset.mul_sum, ← h]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Introduce `k`. Rewrite using `[h0]`. Both sides reduce to the same expression. Set `V : ℕ → Submodule ℂ (Fin A.n → d.R.X → ℂ)` to `fun n => Submodule.span ℂ (Set.range (v n))`. Establish `: ∀ n, FiniteDimensional ℂ (V n)` using `fun n => FiniteDimensional.span_of_finite ℂ (Set.finite_range _)`.

Establish `hrank : ∀ n, Module.finrank ℂ (V n) = (p n).1` using `fun n => (finrank_span_eq_card (hli n)).trans (Fintype.card_fin _)`. Set `eB : ∀ n, Module.Basis (Fin (Module.finrank ℂ (V n))) ℂ (V n)` to `fun n => (Module.Basis.span (hli n)).reindex (finCongr (hrank n).symm)`. Establish `hgram : ∀ (W : Weight L) (m : ConeMetric ℂ (Ix κ)), (∀ y, W.φ (chartIdx A y) y = 2 * Real.log (m.ρ (c y • resPt d y))) → ∀ n, chiGram W dV n (fun a => ((eB n a : V n) : Fin A.n → d.R.X → ℂ)) = -(1 / 2) * Real.log (Matrix.det (fun k l => ∫ y, pairVal m n ((p n).2 k) ((p n).2 l) (r …`. Introduce `W m hW n`. Establish `he : (fun a => ((eB n a : V n) : Fin A.n → d.R.X → ℂ)) = fun a => v n ((finCongr (hrank n).symm).symm a)`.

Use function extensionality and compare the values at `a`. Simplify using `only [eB, Module.Basis.reindex_apply, Module.Basis.span_apply]`. Establish `hsub : gram W dV n (fun a => v n ((finCongr (hrank n).symm).symm a)) = (gram W dV n (v n)).submatrix (finCongr (hrank n).symm).symm (finCongr (hrank n).symm).symm`. Use extensionality with `a a'`. Both sides reduce to the same expression.

Establish `hg : gram W dV n (v n) = fun k l => ∫ y, pairVal m n ((p n).2 k) ((p n).2 l) (resPt d y) ∂d.dV`. Use extensionality with `k l`. Simplify using `only [gram, Matrix.of_apply, hμ, v]`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[hσ y n _ (hhom n k), hσ y n _ (hhom n l), hW y]`. Conclude with `pair_smul m (resPt_ne_zero d y) (hc0 y) (hhom n k) (hhom n l)`. Rewrite using `[chiGram, he, hsub, Matrix.det_submatrix_equiv_self, hg]`. Establish `hC₀ : ∀ n, resCChi d n = -(1 / 2) * Real.log (Matrix.det (fun k l => ∫ y, pairVal d.m n ((p n).2 k) ((p n).2 l) (resPt d y) ∂d.dV : Matrix (Fin (p n).1) (Fin (p n).1) ℂ)).re` using `fun n => by`. Rewrite using `[resCChi, dif_pos (hex n)]`.

Both sides reduce to the same expression. Establish `hC₁ : ∀ n, resCChi (d.withMetric m₁ P0₁ hs hc hle hp) n = -(1 / 2) * Real.log (Matrix.det (fun k l => ∫ y, pairVal m₁ n ((p n).2 k) ((p n).2 l) (resPt d y) ∂d.dV : Matrix (Fin (p n).1) (Fin (p n).1) ℂ)).re` using `fun n => by`. Rewrite using `[resCChi, dif_pos (show ∃ q : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis (d.withMetric m₁ P0₁ hs hc hle hp).x n q.2 from hex n)]`. Both sides reduce to the same expression. Take `⟨mF, hsF, hcF, hpF, hpullF⟩` from `hFS D Ω κ d.x e he`.

Take `⟨-, -, C, -, -, -, -, hr, -⟩` from `hPB D Ω κ (d.withMetric mF ⊥ hsF hcF bot_le hpF) e he hpullF`. Establish `hr' : ∀ n : ℕ, |(Module.finrank ℤ (sec ℤ d.x n) : ℝ) - (projDeg d.x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ)| ≤ C * ((n : ℝ) + 1) ^ (D - 1)` using `hr`. Establish `hsmooth : ∀ t : ℝ, IsSmoothMetric (interp d.m m₁ t)` using `fun t => by show ContDiffOn ℝ _ (fun z => d.m.ρ z ^ (1 - t) * m₁.ρ z ^ t) _`. Conclude with `(d.smooth.rpow_const_of_ne fun z hz => (d.m.pos z hz).ne').mul (hs.rpow_const_of_ne fun z hz => (m₁.pos z hz).ne')`. Establish `hInt : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∫ y, bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ = (projDeg d.x e : ℝ) / (D.factorial : ℝ)`.

Introduce `t ht`. Establish `h` using `hdens t ht (fun _ => 1) continuous_const`. Simplify using `only [one_mul] at h`. Rewrite using `[h, hDeg D Ω κ d e _ he (hsmooth t)]`. Establish `hdim : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (∫ y, bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ - ε) * (n : ℝ) ^ D ≤ Module.finrank ℂ (V n)`.

Introduce `t ht ε hε`. Rewrite using `[hInt t ht]`. Use `filter_upwards [eventually_pow_le C ε hε d.one_le] with n hn`. Rewrite using `[hrank n, (hp' n).card_eq]`. Establish `h` using `(abs_le.1 (hr' n)).1`.

Establish `e1 : ((projDeg d.x e : ℝ) / (D.factorial : ℝ) - ε) * (n : ℝ) ^ D = (projDeg d.x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ) - ε * (n : ℝ) ^ D` using `by ring`. Rewrite using `[e1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hVle : ∀ n, V n ≤ L.sections n` using `fun n => Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hsec n _ (hhom n k))`. Establish `hM` using `hMC A L W₀ W₁ dV hW₀ hW₁ V hVle hdim eB`.

Establish `hdiff : ∀ y, Weight.diff W₁ W₀ y = 2 * logRatio d.m m₁ (resPt d y)`. Introduce `y`. Establish `hz` using `resPt_ne_zero d y`. Establish `hcn : ‖c y‖ ≠ 0` using `norm_ne_zero_iff.2 (hc0 y)`. Rewrite using `[Weight.diff, hφ₁ y, hφ₀ y, logRatio, m₁.smul, d.m.smul, Real.log_mul hcn (m₁.pos _ hz).ne', Real.log_mul hcn (d.m.pos _ hz).ne', Real.log_div (m₁.pos _ hz).ne' (d.m.pos _ hz).ne']`.

Expand and normalize the polynomial expressions, which then agree. Establish `hcont : Continuous fun y => logRatio d.m m₁ (resPt d y)`. Establish `h : (fun y => logRatio d.m m₁ (resPt d y)) = fun y => Weight.diff W₁ W₀ y / 2`. Use function extensionality and compare the values at `y`. Rewrite using `[hdiff]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `(continuous_diff W₁ W₀).div_const 2`. Establish `hK : ∫ t in (0 : ℝ)..1, ∫ y, Weight.diff W₁ W₀ y * bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ = 2 / (D.factorial : ℝ) * resMetricInt d m₁`. Rewrite using `[resMetricInt, ← intervalIntegral.integral_const_mul]`.

Use `intervalIntegral.integral_congr fun t ht => ?_` and prove the remaining obligations. Rewrite `ht` using `[Set.uIcc_of_le zero_le_one]`. Simplify using `only [hdiff]`. Establish `h` using `hdens t ht _ hcont`. Simplify using `only [mul_assoc]`.

Rewrite using `[integral_const_mul, h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[isLittleO_iff]`. Introduce `ε hε`. Use `filter_upwards [hM ε hε] with n hn`.

Rewrite `hn` using `[hgram W₁ m₁ hφ₁ n, hgram W₀ d.m hφ₀ n, hK]`. Rewrite using `[hC₁ n, hC₀ n, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1))]`. Establish `e2 : (n : ℝ) ^ (D + 1) / 2 * (2 / (D.factorial : ℝ) * resMetricInt d m₁) = (n : ℝ) ^ (D + 1) / (D.factorial : ℝ) * resMetricInt d m₁` using `by ring`. Rewrite `hn` using `[e2]`. Conclude with `hn`.
-/
theorem ComplexGramMetricChange.proof (hMC : MetricChange.Statement) (hPB : ProjectionBounds.Statement)
    (hFS : PullFSExtension.Statement) (hPair : ResolutionMetricPair.Statement)
    (hInd : ResolutionFormsIndependent.Statement) (hDeg : ResolutionDegree.Statement) :
    ComplexGramMetricChange.Statement := by
  classical
  intro D Ω _ _ κ _ d m₁ P0₁ hs hc hle hp e he
  obtain ⟨A, L, W₀, W₁, dV, σ, -, hW₀, hW₁, hμ, hsec, hval, hdens⟩ := hPair D Ω κ d m₁ P0₁ hs hle hp
  choose c hc0 hσ hφ₀ hφ₁ using hval

  have hex : ∀ n, ∃ q : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n q.2 := fun n => by
    obtain ⟨b, hb⟩ := exists_isSecBasis d.x n
    exact ⟨⟨_, b⟩, hb⟩
  let p : ℕ → (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ) := fun n => (hex n).choose
  have hp' : ∀ n, IsSecBasis d.x n (p n).2 := fun n => (hex n).choose_spec
  have hhom : ∀ n k, ((p n).2 k).IsHomogeneous n := fun n k => by
    obtain ⟨f, hf, hfe⟩ := (hp' n).1 k
    rw [hfe]
    exact hf.map _
  let v : ∀ n, Fin (p n).1 → Fin A.n → d.R.X → ℂ := fun n k => σ n ((p n).2 k)
  have hli : ∀ n, LinearIndependent ℂ (v n) := by
    intro n
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : g = 0 := hInd D Ω κ d n _ (p n).2 (hp' n) g fun y => by
      have h := congrFun (congrFun hg (chartIdx A y)) y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v,
        hσ y n _ (hhom n _), eval_smul_of_homog ((hhom n _).map _)] at h
      have hcn : c y ^ n ≠ 0 := pow_ne_zero _ (hc0 y)
      apply (mul_right_inj' hcn).1
      rw [mul_zero, Finset.mul_sum, ← h]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    intro k
    rw [h0]
    rfl
  let V : ℕ → Submodule ℂ (Fin A.n → d.R.X → ℂ) := fun n => Submodule.span ℂ (Set.range (v n))
  have : ∀ n, FiniteDimensional ℂ (V n) := fun n => FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hrank : ∀ n, Module.finrank ℂ (V n) = (p n).1 := fun n =>
    (finrank_span_eq_card (hli n)).trans (Fintype.card_fin _)
  let eB : ∀ n, Module.Basis (Fin (Module.finrank ℂ (V n))) ℂ (V n) := fun n =>
    (Module.Basis.span (hli n)).reindex (finCongr (hrank n).symm)

  have hgram : ∀ (W : Weight L) (m : ConeMetric ℂ (Ix κ)),
      (∀ y, W.φ (chartIdx A y) y = 2 * Real.log (m.ρ (c y • resPt d y))) → ∀ n,
      chiGram W dV n (fun a => ((eB n a : V n) : Fin A.n → d.R.X → ℂ)) =
        -(1 / 2) * Real.log (Matrix.det (fun k l => ∫ y, pairVal m n ((p n).2 k) ((p n).2 l) (resPt d y) ∂d.dV :
          Matrix (Fin (p n).1) (Fin (p n).1) ℂ)).re := by
    intro W m hW n
    have he : (fun a => ((eB n a : V n) : Fin A.n → d.R.X → ℂ)) = fun a => v n ((finCongr (hrank n).symm).symm a) := by
      funext a
      simp only [eB, Module.Basis.reindex_apply, Module.Basis.span_apply]
    have hsub : gram W dV n (fun a => v n ((finCongr (hrank n).symm).symm a)) =
        (gram W dV n (v n)).submatrix (finCongr (hrank n).symm).symm (finCongr (hrank n).symm).symm := by
      ext a a'
      rfl
    have hg : gram W dV n (v n) = fun k l => ∫ y, pairVal m n ((p n).2 k) ((p n).2 l) (resPt d y) ∂d.dV := by
      ext k l
      simp only [gram, Matrix.of_apply, hμ, v]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only
      rw [hσ y n _ (hhom n k), hσ y n _ (hhom n l), hW y]
      exact pair_smul m (resPt_ne_zero d y) (hc0 y) (hhom n k) (hhom n l)
    rw [chiGram, he, hsub, Matrix.det_submatrix_equiv_self, hg]
  have hC₀ : ∀ n, resCChi d n = -(1 / 2) * Real.log (Matrix.det (fun k l =>
      ∫ y, pairVal d.m n ((p n).2 k) ((p n).2 l) (resPt d y) ∂d.dV :
        Matrix (Fin (p n).1) (Fin (p n).1) ℂ)).re := fun n => by
    rw [resCChi, dif_pos (hex n)]
    rfl
  have hC₁ : ∀ n, resCChi (d.withMetric m₁ P0₁ hs hc hle hp) n = -(1 / 2) * Real.log (Matrix.det (fun k l =>
      ∫ y, pairVal m₁ n ((p n).2 k) ((p n).2 l) (resPt d y) ∂d.dV :
        Matrix (Fin (p n).1) (Fin (p n).1) ℂ)).re := fun n => by
    rw [resCChi, dif_pos (show ∃ q : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ),
      IsSecBasis (d.withMetric m₁ P0₁ hs hc hle hp).x n q.2 from hex n)]
    rfl

  obtain ⟨mF, hsF, hcF, hpF, hpullF⟩ := hFS D Ω κ d.x e he
  obtain ⟨-, -, C, -, -, -, -, hr, -⟩ := hPB D Ω κ (d.withMetric mF ⊥ hsF hcF bot_le hpF) e he hpullF
  have hr' : ∀ n : ℕ, |(Module.finrank ℤ (sec ℤ d.x n) : ℝ) - (projDeg d.x e : ℝ) * (n : ℝ) ^ D /
      (D.factorial : ℝ)| ≤ C * ((n : ℝ) + 1) ^ (D - 1) := hr
  have hsmooth : ∀ t : ℝ, IsSmoothMetric (interp d.m m₁ t) := fun t => by
    show ContDiffOn ℝ _ (fun z => d.m.ρ z ^ (1 - t) * m₁.ρ z ^ t) _
    exact (d.smooth.rpow_const_of_ne fun z hz => (d.m.pos z hz).ne').mul
      (hs.rpow_const_of_ne fun z hz => (m₁.pos z hz).ne')
  have hInt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∫ y, bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ = (projDeg d.x e : ℝ) / (D.factorial : ℝ) := by
    intro t ht
    have h := hdens t ht (fun _ => 1) continuous_const
    simp only [one_mul] at h
    rw [h, hDeg D Ω κ d e _ he (hsmooth t)]
  have hdim : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (∫ y, bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ - ε) * (n : ℝ) ^ D ≤ Module.finrank ℂ (V n) := by
    intro t ht ε hε
    rw [hInt t ht]
    filter_upwards [eventually_pow_le C ε hε d.one_le] with n hn
    rw [hrank n, (hp' n).card_eq]
    have h := (abs_le.1 (hr' n)).1
    have e1 : ((projDeg d.x e : ℝ) / (D.factorial : ℝ) - ε) * (n : ℝ) ^ D =
        (projDeg d.x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ) - ε * (n : ℝ) ^ D := by ring
    rw [e1]
    linarith
  have hVle : ∀ n, V n ≤ L.sections n := fun n =>
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hsec n _ (hhom n k))
  have hM := hMC A L W₀ W₁ dV hW₀ hW₁ V hVle hdim eB

  have hdiff : ∀ y, Weight.diff W₁ W₀ y = 2 * logRatio d.m m₁ (resPt d y) := by
    intro y
    have hz := resPt_ne_zero d y
    have hcn : ‖c y‖ ≠ 0 := norm_ne_zero_iff.2 (hc0 y)
    rw [Weight.diff, hφ₁ y, hφ₀ y, logRatio, m₁.smul, d.m.smul, Real.log_mul hcn (m₁.pos _ hz).ne',
      Real.log_mul hcn (d.m.pos _ hz).ne', Real.log_div (m₁.pos _ hz).ne' (d.m.pos _ hz).ne']
    ring
  have hcont : Continuous fun y => logRatio d.m m₁ (resPt d y) := by
    have h : (fun y => logRatio d.m m₁ (resPt d y)) = fun y => Weight.diff W₁ W₀ y / 2 := by
      funext y
      rw [hdiff]
      ring
    rw [h]
    exact (continuous_diff W₁ W₀).div_const 2
  have hK : ∫ t in (0 : ℝ)..1, ∫ y, Weight.diff W₁ W₀ y * bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ =
      2 / (D.factorial : ℝ) * resMetricInt d m₁ := by
    rw [resMetricInt, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    simp only [hdiff]
    have h := hdens t ht _ hcont
    simp only [mul_assoc]
    rw [integral_const_mul, h]
    ring

  rw [isLittleO_iff]
  intro ε hε
  filter_upwards [hM ε hε] with n hn
  rw [hgram W₁ m₁ hφ₁ n, hgram W₀ d.m hφ₀ n, hK] at hn
  rw [hC₁ n, hC₀ n, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1))]
  have e2 : (n : ℝ) ^ (D + 1) / 2 * (2 / (D.factorial : ℝ) * resMetricInt d m₁) =
      (n : ℝ) ^ (D + 1) / (D.factorial : ℝ) * resMetricInt d m₁ := by ring
  rw [e2] at hn
  exact hn

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
