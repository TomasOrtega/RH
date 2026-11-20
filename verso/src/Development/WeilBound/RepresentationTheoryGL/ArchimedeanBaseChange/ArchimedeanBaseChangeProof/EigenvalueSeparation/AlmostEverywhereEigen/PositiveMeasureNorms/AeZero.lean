import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf

open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

noncomputable section

namespace PositivityTheory.Rg.BcB.E2.P.Spec

/- English proof (translation)
Rewrite `hi` using `[integral_complex_ofReal, Complex.ofReal_eq_zero]`. Establish `hint : Integrable u ν` using `integrableOn_univ.1 (hu.continuousOn.integrableOn_compact isCompact_univ)`. Conclude with `(integral_eq_zero_iff_of_nonneg (fun s => h0 s) hint).1 hi`.
-/
theorem ae_zero {S : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
    (ν : Measure S) [IsFiniteMeasure ν] [ν.Regular] (u : S → ℝ) (hu : Continuous u) (h0 : ∀ s, 0 ≤ u s)
    (hi : ∫ s, (u s : ℂ) ∂ν = 0) : ∀ᵐ s ∂ν, u s = 0 := by
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hi
  have hint : Integrable u ν := integrableOn_univ.1 (hu.continuousOn.integrableOn_compact isCompact_univ)
  exact (integral_eq_zero_iff_of_nonneg (fun s => h0 s) hint).1 hi

end PositivityTheory.Rg.BcB.E2.P.Spec

namespace PositivityTheory.Rg.BcB.E2.P

open PositivityTheory.Rg.BcB.E2.P.Spec in
/- English proof (translation)
Introduce `hG hP hM hI K _ _ _ B _ _ _ _ R p C₀ ε hp hε`. Take `⟨S, _, _, _, π, e, hπ, he⟩` from `hG K B R`. Establish `hne : ∀ b, ‖e b‖ = ‖R b‖` using `fun b => by rw [← hπ, he]`. Take `⟨s₀, hs₀⟩` from `hP B S e p fun b => (hp b).trans (hne b).ge`. Set `_ : MeasurableSpace S` to `borel S`.

Establish `: BorelSpace S` using `⟨rfl⟩`. Set `gr : S → ℝ` to `fun s => max 0 (1 - (2 / ε) * ∑ c ∈ C₀, ‖e c s - p c‖)`. Establish `hgr : Continuous gr`. Use `continuous_const.max (continuous_const.sub (continuous_const.mul ?_))` and prove the remaining obligations. Conclude with `continuous_finsetSum _ fun c _ => continuous_norm.comp ((e c).continuous.sub continuous_const)`.

Set `g : C(S, ℂ)` to `⟨fun s => (gr s : ℂ), Complex.continuous_ofReal.comp hgr⟩`. Establish `hg0 : g s₀ = 1`. Simplify using `[g, gr, hs₀]`. Establish `hgne : π g ≠ 0`. Introduce `h`.

Establish `h1 : ‖g‖ = 0` using `by rw [← hπ, h, norm_zero]`. Establish `h2` using `ContinuousMap.norm_coe_le_norm g s₀`. Rewrite `h2` using `[hg0, h1]`. Evaluate the numerical expressions using `at h2`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, π g v ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hgne (ContinuousLinearMap.ext h)`. Use `set w := π g v with hw`. Take `⟨ν, hνf, hνr, hν⟩` from `hM K S π w`.

Take `⟨V, hViso, hVmul⟩` from `hI K S π w ν hν`. Set `χ : S → (B →⋆ₐ[ℂ] ℂ)` to `fun s => (ContinuousMap.evalStarAlgHom ℂ ℂ s).comp e`. Establish `hχ : ∀ s b, χ s b = e b s` using `fun s b => rfl`. Use `⟨S, borel S, ν, hνf, χ, V, ⟨?_, ?_, ?_, hViso, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Establish `h1` using `hν 1`. Rewrite `h1` using `[h0, integral_zero_measure, map_one, ContinuousLinearMap.one_apply]`. Conclude with `hv (inner_self_eq_zero.1 h1.symm)`. Introduce `b`. Simplify using `only [hχ]`.

Conclude with `(e b).continuous.measurable`. Introduce `b s`. Rewrite using `[hχ, ← hne]`. Conclude with `ContinuousMap.norm_coe_le_norm _ _`. Introduce `b h h' hh`.

Rewrite using `[← he]`. Conclude with `hVmul (e b) h h' (by simpa only [hχ] using hh)`. Rewrite using `[Filter.eventually_all_finset]`. Introduce `c hc`. Set `tr : S → ℝ` to `fun s => max 0 (‖e c s - p c‖ - ε)`.

Establish `htr : Continuous tr` using `continuous_const.max ((continuous_norm.comp ((e c).continuous.sub continuous_const)).sub continuous_const)`. Set `t : C(S, ℂ)` to `⟨fun s => (tr s : ℂ), Complex.continuous_ofReal.comp htr⟩`. Establish `htg : t * g = 0`. Use extensionality with `s`. Simplify using `only [ContinuousMap.mul_apply, ContinuousMap.zero_apply, t, g, ContinuousMap.coe_mk]`.

Break down `le_or_gt (‖e c s - p c‖) ε with h | h` into its components or cases. Establish `: tr s = 0` using `max_eq_left (by linarith)`. Simplify using `[this]`. Establish `hs : ‖e c s - p c‖ ≤ ∑ c ∈ C₀, ‖e c s - p c‖` using `Finset.single_le_sum (f := fun c => ‖e c s - p c‖) (fun _ _ => norm_nonneg _) hc`. Establish `h2 : 2 < (2 / ε) * ∑ c ∈ C₀, ‖e c s - p c‖`.

Rewrite using `[div_mul_eq_mul_div, lt_div_iff₀ hε]`. Use the polynomial consequences of the given equalities and inequalities. Establish `: gr s = 0` using `max_eq_left (by linarith)`. Simplify using `[this]`. Establish `hint : ∫ s, (tr s : ℂ) ∂ν = 0`.

Establish `h1` using `hν t`. Establish `h2 : π t w = 0`. Rewrite using `[hw, ← ContinuousLinearMap.mul_apply, ← map_mul, htg, map_zero, ContinuousLinearMap.zero_apply]`. Rewrite `h1` using `[h2, inner_zero_right]`. Conclude with `h1`.

Use `filter_upwards [ae_zero ν tr htr (fun s => le_max_left _ _) hint] with s hs`. Rewrite using `[hχ]`. Establish `: ‖e c s - p c‖ - ε ≤ 0` using `max_eq_left_iff.1 hs`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem spec : Gelf → Point → SpecMeas → SpecIso → Spec := by
  classical
  intro hG hP hM hI K _ _ _ B _ _ _ _ R p C₀ ε hp hε
  obtain ⟨S, _, _, _, π, e, hπ, he⟩ := hG K B R
  have hne : ∀ b, ‖e b‖ = ‖R b‖ := fun b => by rw [← hπ, he]
  obtain ⟨s₀, hs₀⟩ := hP B S e p fun b => (hp b).trans (hne b).ge
  let _ : MeasurableSpace S := borel S
  have : BorelSpace S := ⟨rfl⟩

  let gr : S → ℝ := fun s => max 0 (1 - (2 / ε) * ∑ c ∈ C₀, ‖e c s - p c‖)
  have hgr : Continuous gr := by
    refine continuous_const.max (continuous_const.sub (continuous_const.mul ?_))
    exact continuous_finsetSum _ fun c _ => continuous_norm.comp ((e c).continuous.sub continuous_const)
  let g : C(S, ℂ) := ⟨fun s => (gr s : ℂ), Complex.continuous_ofReal.comp hgr⟩
  have hg0 : g s₀ = 1 := by
    simp [g, gr, hs₀]
  have hgne : π g ≠ 0 := by
    intro h
    have h1 : ‖g‖ = 0 := by rw [← hπ, h, norm_zero]
    have h2 := ContinuousMap.norm_coe_le_norm g s₀
    rw [hg0, h1] at h2
    norm_num at h2
  obtain ⟨v, hv⟩ : ∃ v, π g v ≠ 0 := by
    by_contra h
    push Not at h
    exact hgne (ContinuousLinearMap.ext h)
  set w := π g v with hw
  obtain ⟨ν, hνf, hνr, hν⟩ := hM K S π w
  obtain ⟨V, hViso, hVmul⟩ := hI K S π w ν hν
  let χ : S → (B →⋆ₐ[ℂ] ℂ) := fun s => (ContinuousMap.evalStarAlgHom ℂ ℂ s).comp e
  have hχ : ∀ s b, χ s b = e b s := fun s b => rfl
  refine ⟨S, borel S, ν, hνf, χ, V, ⟨?_, ?_, ?_, hViso, ?_⟩, ?_⟩
  · intro h0
    have h1 := hν 1
    rw [h0, integral_zero_measure, map_one, ContinuousLinearMap.one_apply] at h1
    exact hv (inner_self_eq_zero.1 h1.symm)
  · intro b
    simp only [hχ]
    exact (e b).continuous.measurable
  · intro b s
    rw [hχ, ← hne]
    exact ContinuousMap.norm_coe_le_norm _ _
  · intro b h h' hh
    rw [← he]
    exact hVmul (e b) h h' (by simpa only [hχ] using hh)
  · rw [Filter.eventually_all_finset]
    intro c hc
    let tr : S → ℝ := fun s => max 0 (‖e c s - p c‖ - ε)
    have htr : Continuous tr :=
      continuous_const.max ((continuous_norm.comp ((e c).continuous.sub continuous_const)).sub continuous_const)
    let t : C(S, ℂ) := ⟨fun s => (tr s : ℂ), Complex.continuous_ofReal.comp htr⟩
    have htg : t * g = 0 := by
      ext s
      simp only [ContinuousMap.mul_apply, ContinuousMap.zero_apply, t, g, ContinuousMap.coe_mk]
      rcases le_or_gt (‖e c s - p c‖) ε with h | h
      · have : tr s = 0 := max_eq_left (by linarith)
        simp [this]
      · have hs : ‖e c s - p c‖ ≤ ∑ c ∈ C₀, ‖e c s - p c‖ :=
          Finset.single_le_sum (f := fun c => ‖e c s - p c‖) (fun _ _ => norm_nonneg _) hc
        have h2 : 2 < (2 / ε) * ∑ c ∈ C₀, ‖e c s - p c‖ := by
          rw [div_mul_eq_mul_div, lt_div_iff₀ hε]
          nlinarith
        have : gr s = 0 := max_eq_left (by linarith)
        simp [this]
    have hint : ∫ s, (tr s : ℂ) ∂ν = 0 := by
      have h1 := hν t
      have h2 : π t w = 0 := by
        rw [hw, ← ContinuousLinearMap.mul_apply, ← map_mul, htg, map_zero, ContinuousLinearMap.zero_apply]
      rw [h2, inner_zero_right] at h1
      exact h1
    filter_upwards [ae_zero ν tr htr (fun s => le_max_left _ _) hint] with s hs
    rw [hχ]
    have : ‖e c s - p c‖ - ε ≤ 0 := max_eq_left_iff.1 hs
    linarith

end PositivityTheory.Rg.BcB.E2.P

end
