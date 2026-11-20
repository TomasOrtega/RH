import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentCoefficientShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.EmbeddingHermitianPairs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.AdmissibleHermitianColumns
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMeanContinuity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bExpHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bNormHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LogDOfPosBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankEqTwoMulHalfDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay

namespace ReciprocityTheory.ChartRestriction.G.FD.flowTermNormDecay

open NumberField Complex Filter
open scoped ComplexConjugate Topology Real

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Apply `UnipotentCoefficientShift.eq_zero_of_conj_lt_one (X.L'_int v hv v hv)` to reduce the goal to its premises. Establish `key : ∀ τ : X.Ψ, ‖τ.1 (herm X.Gm v v)‖ < 1`. Introduce `τ`. Establish `h` using `lt_of_le_of_lt (UnipotentCoefficientShift.norm_hermC_le_maj (hz := hz0) (τ := τ) (v := Data.emb τ.1 v)) (hsmall τ)`. Establish `e : hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 v) = τ.1 (herm X.Gm v v)` using `EmbeddingHermitianPairs.hermC_emb (x := v) (y := v) ..`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis. Introduce `σ`. Distinguish the cases in `hσ : σ ∈ X.Ψ`. Conclude with `key ⟨σ, hσ⟩`. Establish `hc : NumberField.ComplexEmbedding.conjugate σ ∈ X.Ψ`.

Assume the negation of the conclusion as `h`. Conclude with `hσ ((X.cmType σ).2 h)`. Establish `h` using `key ⟨_, hc⟩`. Simplify `h` using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`.
-/
theorem herm_eq_zero (X : DataX E r) {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.dom) {v : Fin r → E}
    (hv : v ∈ X.L') (hsmall : ∀ τ : X.Ψ, X.maj z0 τ (Data.emb τ.1 v) < 1) : herm X.Gm v v = 0 := by
  apply UnipotentCoefficientShift.eq_zero_of_conj_lt_one (X.L'_int v hv v hv)
  have key : ∀ τ : X.Ψ, ‖τ.1 (herm X.Gm v v)‖ < 1 := by
    intro τ
    have h := lt_of_le_of_lt
      (UnipotentCoefficientShift.norm_hermC_le_maj (hz := hz0) (τ := τ) (v := Data.emb τ.1 v)) (hsmall τ)
    have e : hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 v) = τ.1 (herm X.Gm v v) :=
      EmbeddingHermitianPairs.hermC_emb (x := v) (y := v) ..
    rwa [e] at h
  intro σ
  by_cases hσ : σ ∈ X.Ψ
  · exact key ⟨σ, hσ⟩
  · have hc : NumberField.ComplexEmbedding.conjugate σ ∈ X.Ψ := by
      by_contra h
      exact hσ ((X.cmType σ).2 h)
    have h := key ⟨_, hc⟩
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using h

/- English proof (translation)
Unfold `herm cc`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_nsmul (G : Matrix (Fin r) (Fin r) E) (n : ℕ) (v : Fin r → E) :
    herm G ((n : E) • v) ((n : E) • v) = (n : E) * n * herm G v v := by
  unfold herm cc
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Data.flowMat, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]`. Simplify using `only [mul_left_comm _ (n : ℂ), ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem flowMat_nsmul (X : Data E r) (v : Fin r → E) (n : ℕ) (τ : X.Ψ) (s : ℂ) :
    X.flowMat ((n : E) • v) τ s = X.flowMat v τ ((n : ℂ) ^ 2 * s) := by
  ext a b
  simp only [Data.flowMat, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
  simp only [mul_left_comm _ (n : ℂ), ← Finset.mul_sum]
  ring

/- English proof (translation)
Unfold `Data.nfac`. Use `Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _` and prove the remaining obligations. Establish `hne : ∀ j : Fin (r + 1), dmin X.Gm x τ j ≠ 0` using `fun j h => by`. Use `(hx τ).2 j` as an intermediate fact. Rewrite `this` using `[h, Complex.zero_re, mul_zero]`.

Conclude with `lt_irrefl 0 this`. Conclude with `norm_pos_iff.mpr (div_ne_zero (hne _) (hne _))`.
-/
theorem nfac_pos (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < X.nfac la x := by
  unfold Data.nfac
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
  have hne : ∀ j : Fin (r + 1), dmin X.Gm x τ j ≠ 0 := fun j h => by
    have := (hx τ).2 j
    rw [h, Complex.zero_re, mul_zero] at this
    exact lt_irrefl 0 this
  exact norm_pos_iff.mpr (div_ne_zero (hne _) (hne _))

/- English proof (translation)
Establish `h : (4 * π * I * ∑ τ, (ν τ : ℂ) * (ζ / (n : ℂ) ^ 2)) = I * (((4 * π * (∑ τ, ν τ) / (n : ℝ) ^ 2 : ℝ)) : ℂ) * ζ`. Rewrite using `[← Finset.sum_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[norm_mul, h, Complex.norm_exp]`.

Use `congr 2`. Simplify using `only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem term_norm {ι : Type*} [Fintype ι] (c : ℂ) (ν : ι → ℝ) (ζ : ℂ) (n : ℕ) :
    ‖c * cexp (4 * π * I * ∑ τ, (ν τ : ℂ) * (ζ / (n : ℂ) ^ 2))‖ =
      ‖c‖ * Real.exp (-(4 * π * (∑ τ, ν τ) / (n : ℝ) ^ 2 * ζ.im)) := by
  have h : (4 * π * I * ∑ τ, (ν τ : ℂ) * (ζ / (n : ℂ) ^ 2)) =
      I * (((4 * π * (∑ τ, ν τ) / (n : ℝ) ^ 2 : ℝ)) : ℂ) * ζ := by
    rw [← Finset.sum_mul]
    push_cast
    ring
  rw [norm_mul, h, Complex.norm_exp]
  congr 2
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/- English proof (translation)
Use `set n := X.NC with hn`. Establish `hn0 : (n : ℂ) ≠ 0` using `by exact_mod_cast X.NC_pos.ne'`. Use `set ξ : Fin r → E := (n : E) • v with hξdef`. Establish `hξ : X.IsIso ξ`. Use `⟨X.NC_sub v hv, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hξdef, herm_nsmul, hvv, mul_zero]`. Conclude with `smul_ne_zero (by exact_mod_cast X.NC_pos.ne') hv0`. Establish `hflow : ∀ ζ : ℂ, X.flow v (fun _ => ζ) z0 = X.flow ξ (fun _ => ζ / (n : ℂ) ^ 2) z0`. Introduce `ζ`. Use function extensionality and compare the values at `τ`.

Simplify using `only [Data.flow]`. Rewrite using `[flowMat_nsmul]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts. Use `set a : (X.Ψ → ℝ) → ℂ := fun ν => X.fj la ξ ν P z0 with ha`.

Establish `hexp : ∀ ζ : ℂ, 0 ≤ ζ.im → HasSum (fun ν : X.Ψ → ℝ => a ν * cexp (4 * π * I * ∑ τ, (ν τ : ℂ) * (ζ / (n : ℂ) ^ 2))) (P (X.flow v (fun _ => ζ) z0))`. Introduce `ζ hζ`. Rewrite using `[hflow]`. Conclude with `m3bExp_holds r X.toData la P hP.1.1 ξ hξ z0 hz0 (fun _ => ζ / (n : ℂ) ^ 2) (by rw [← hflow]; exact hdom ζ hζ)`. Take `⟨C, hC⟩` from `hP.1.2`.

Establish `hpos` using `(moderateCoefficientPositivity_holds r X.toData la P C 0 hP.1.1 (fun x hx => by simpa using hC x hx)).1`. Establish `ha0 : a 0 = 0` using `hP.2 ξ hξ z0 hz0`. Establish `hS : ∀ ν, a ν ≠ 0 → 0 < ∑ τ, ν τ`. Introduce `ν hν`. Establish `hnn : ∀ τ, 0 ≤ ν τ` using `hpos ξ hξ ν z0 hz0 hν`.

Establish `hne : ν ≠ 0`. Introduce and unpack `rfl`. Conclude with `hν ha0`. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : ∃ τ, ν τ ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Conclude with `hne (funext h)`. Conclude with `Finset.sum_pos' (fun τ _ => hnn τ) ⟨τ, Finset.mem_univ _, lt_of_le_of_ne (hnn τ) (Ne.symm hτ)⟩`. Establish `hsum : Summable fun ν => ‖a ν‖`. Establish `h0` using `(hexp 0 (le_refl _)).summable`.

Simplify using `only [zero_div, mul_zero, Finset.sum_const_zero, Complex.exp_zero, mul_one] at h0`. Conclude with `summable_norm_iff.2 h0`. Establish `hab : ∀ ν : X.Ψ → ℝ, Tendsto (fun ζ : ℂ => a ν * cexp (4 * π * I * ∑ τ, (ν τ : ℂ) * (ζ / (n : ℂ) ^ 2))) (comap im atTop) (𝓝 0)`. Introduce `ν`. Distinguish the cases in `hν : a ν = 0`.

Simplify using `only [hν, zero_mul]`. Conclude with `tendsto_const_nhds`. Rewrite using `[tendsto_zero_iff_norm_tendsto_zero]`. Simplify using `only [term_norm]`. Establish `hk : 0 < 4 * π * (∑ τ, ν τ) / (n : ℝ) ^ 2`.

Use `hS ν hν` as an intermediate fact. Establish `: (0 : ℝ) < n` using `by exact_mod_cast X.NC_pos`. Check the signs of the components of the expression. Establish `h1 : Tendsto (fun ζ : ℂ => ζ.im) (comap im atTop) atTop` using `tendsto_comap`. Establish `h2` using `Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (h1.const_mul_atTop hk))`.

Establish `h3` using `h2.const_mul ‖a ν‖`. Simplify using `using h3`. Establish `hbound : ∀ᶠ ζ in comap im atTop, ∀ ν : X.Ψ → ℝ, ‖a ν * cexp (4 * π * I * ∑ τ, (ν τ : ℂ) * (ζ / (n : ℂ) ^ 2))‖ ≤ ‖a ν‖`. Establish `hev : ∀ᶠ ζ in comap im atTop, (0 : ℝ) ≤ ζ.im` using `tendsto_comap.eventually (eventually_ge_atTop 0)`. Use `filter_upwards [hev] with ζ hζ ν`.

Rewrite using `[term_norm]`. Distinguish the cases in `hν : a ν = 0`. Simplify using `[hν]`. Establish `hk : 0 ≤ 4 * π * (∑ τ, ν τ) / (n : ℝ) ^ 2`. Use `hS ν hν` as an intermediate fact.

Check the signs of the components of the expression. Use `mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)` and prove the remaining obligations. Use `mul_nonneg hk hζ` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT` using `tendsto_tsum_of_dominated_convergence hsum hab hbound`.

Simplify using `only [tsum_zero] at hT`. Use `hT.congr' ?_` and prove the remaining obligations. Establish `hev : ∀ᶠ ζ in comap im atTop, (0 : ℝ) < ζ.im` using `tendsto_comap.eventually (eventually_gt_atTop 0)`. Use `filter_upwards [hev] with ζ hζ`. Rewrite using `[hG ζ hζ]`.

Conclude with `(hexp ζ hζ.le).tsum_eq`.
-/
theorem tendsto_zero (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : P ∈ X.SS la)
    {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.dom) {v : Fin r → E} (hv : v ∈ X.L')
    (hvv : herm X.Gm v v = 0) (hv0 : v ≠ 0)
    (hdom : ∀ ζ : ℂ, 0 ≤ ζ.im → X.flow v (fun _ => ζ) z0 ∈ X.dom) (G : ℂ → ℂ)
    (hG : ∀ ζ : ℂ, 0 < ζ.im → G ζ = P (X.flow v (fun _ => ζ) z0)) :
    Tendsto G (comap im atTop) (𝓝 0) := by
  classical
  set n := X.NC with hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast X.NC_pos.ne'
  set ξ : Fin r → E := (n : E) • v with hξdef
  have hξ : X.IsIso ξ := by
    refine ⟨X.NC_sub v hv, ?_, ?_⟩
    · rw [hξdef, herm_nsmul, hvv, mul_zero]
    · exact smul_ne_zero (by exact_mod_cast X.NC_pos.ne') hv0
  have hflow : ∀ ζ : ℂ, X.flow v (fun _ => ζ) z0 = X.flow ξ (fun _ => ζ / (n : ℂ) ^ 2) z0 := by
    intro ζ
    funext τ
    simp only [Data.flow]
    rw [flowMat_nsmul]
    congr 2
    field_simp
  set a : (X.Ψ → ℝ) → ℂ := fun ν => X.fj la ξ ν P z0 with ha
  have hexp : ∀ ζ : ℂ, 0 ≤ ζ.im → HasSum (fun ν : X.Ψ → ℝ =>
      a ν * cexp (4 * π * I * ∑ τ, (ν τ : ℂ) * (ζ / (n : ℂ) ^ 2))) (P (X.flow v (fun _ => ζ) z0)) := by
    intro ζ hζ
    rw [hflow]
    exact m3bExp_holds r X.toData la P hP.1.1 ξ hξ z0 hz0 (fun _ => ζ / (n : ℂ) ^ 2)
      (by rw [← hflow]; exact hdom ζ hζ)
  obtain ⟨C, hC⟩ := hP.1.2
  have hpos := (moderateCoefficientPositivity_holds r X.toData la P C 0 hP.1.1 (fun x hx => by simpa using hC x hx)).1
  have ha0 : a 0 = 0 := hP.2 ξ hξ z0 hz0
  have hS : ∀ ν, a ν ≠ 0 → 0 < ∑ τ, ν τ := by
    intro ν hν
    have hnn : ∀ τ, 0 ≤ ν τ := hpos ξ hξ ν z0 hz0 hν
    have hne : ν ≠ 0 := by
      rintro rfl
      exact hν ha0
    obtain ⟨τ, hτ⟩ : ∃ τ, ν τ ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    exact Finset.sum_pos' (fun τ _ => hnn τ) ⟨τ, Finset.mem_univ _, lt_of_le_of_ne (hnn τ) (Ne.symm hτ)⟩
  have hsum : Summable fun ν => ‖a ν‖ := by
    have h0 := (hexp 0 (le_refl _)).summable
    simp only [zero_div, mul_zero, Finset.sum_const_zero, Complex.exp_zero, mul_one] at h0
    exact summable_norm_iff.2 h0
  have hab : ∀ ν : X.Ψ → ℝ, Tendsto (fun ζ : ℂ =>
      a ν * cexp (4 * π * I * ∑ τ, (ν τ : ℂ) * (ζ / (n : ℂ) ^ 2))) (comap im atTop) (𝓝 0) := by
    intro ν
    by_cases hν : a ν = 0
    · simp only [hν, zero_mul]
      exact tendsto_const_nhds
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [term_norm]
    have hk : 0 < 4 * π * (∑ τ, ν τ) / (n : ℝ) ^ 2 := by
      have := hS ν hν
      have : (0 : ℝ) < n := by exact_mod_cast X.NC_pos
      positivity
    have h1 : Tendsto (fun ζ : ℂ => ζ.im) (comap im atTop) atTop := tendsto_comap
    have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (h1.const_mul_atTop hk))
    have h3 := h2.const_mul ‖a ν‖
    simpa using h3
  have hbound : ∀ᶠ ζ in comap im atTop, ∀ ν : X.Ψ → ℝ,
      ‖a ν * cexp (4 * π * I * ∑ τ, (ν τ : ℂ) * (ζ / (n : ℂ) ^ 2))‖ ≤ ‖a ν‖ := by
    have hev : ∀ᶠ ζ in comap im atTop, (0 : ℝ) ≤ ζ.im :=
      tendsto_comap.eventually (eventually_ge_atTop 0)
    filter_upwards [hev] with ζ hζ ν
    rw [term_norm]
    by_cases hν : a ν = 0
    · simp [hν]
    have hk : 0 ≤ 4 * π * (∑ τ, ν τ) / (n : ℝ) ^ 2 := by
      have := hS ν hν
      positivity
    refine mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
    have := mul_nonneg hk hζ
    linarith
  have hT := tendsto_tsum_of_dominated_convergence hsum hab hbound
  simp only [tsum_zero] at hT
  refine hT.congr' ?_
  have hev : ∀ᶠ ζ in comap im atTop, (0 : ℝ) < ζ.im :=
    tendsto_comap.eventually (eventually_gt_atTop 0)
  filter_upwards [hev] with ζ hζ
  rw [hG ζ hζ]
  exact (hexp ζ hζ.le).tsum_eq

/- English proof (translation)
Break down `isEmpty_or_nonempty (Fin r) with h | ⟨⟨i⟩⟩` into its components or cases. Simplify using `[Data.spread, Real.iSup_of_isEmpty, Real.iInf_of_isEmpty]`. Unfold `Data.spread`. Establish `h1` using `ciInf_le (Set.finite_range fun i => (la τ i : ℝ)).bddBelow i`. Establish `h2` using `le_ciSup (Set.finite_range fun i => (la τ i : ℝ)).bddAbove i`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem spread_nonneg' (X : Data E r) (la : Wt X.Ψ r) (τ : X.Ψ) : 0 ≤ X.spread la τ := by
  rcases isEmpty_or_nonempty (Fin r) with h | ⟨⟨i⟩⟩
  · simp [Data.spread, Real.iSup_of_isEmpty, Real.iInf_of_isEmpty]
  · unfold Data.spread
    have h1 := ciInf_le (Set.finite_range fun i => (la τ i : ℝ)).bddBelow i
    have h2 := le_ciSup (Set.finite_range fun i => (la τ i : ℝ)).bddAbove i
    linarith

end ReciprocityTheory.ChartRestriction.G.FD.flowTermNormDecay
