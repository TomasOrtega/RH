import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.Glob

namespace SchwartzDifferenceQuotient

variable {m n : ℕ}

instance haarInner (n : ℕ) : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

instance haarOuter (m n : ℕ) : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

/- English proof (translation)
Take `⟨S, rfl⟩` from `hf`. Take `⟨S', rfl⟩` from `hg`. Conclude with `⟨S - S', by ext u; simp⟩`.
-/
theorem isSch_sub {f g : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) (hg : IsSch g) : IsSch (f - g) := by
  obtain ⟨S, rfl⟩ := hf
  obtain ⟨S', rfl⟩ := hg
  exact ⟨S - S', by ext u; simp⟩

/- English proof (translation)
Take `⟨S, rfl⟩` from `hf`. Conclude with `⟨a • S, by ext u; simp [smul_eq_mul]⟩`.
-/
theorem isSch_smul (a : ℂ) {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) : IsSch (fun u => a * f u) := by
  obtain ⟨S, rfl⟩ := hf
  exact ⟨a • S, by ext u; simp [smul_eq_mul]⟩

/- English proof (translation)
Take `⟨S, rfl⟩` from `hf`. Conclude with `S.continuous`.
-/
theorem isSch_continuous {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) : Continuous f := by
  obtain ⟨S, rfl⟩ := hf
  exact S.continuous

/- English proof (translation)
Take `⟨S, rfl⟩` from `hf`. Conclude with `(S.memLp ((2 : ℕ) : ENNReal) volume).integrable_norm_pow two_ne_zero`.
-/
theorem isSch_sq_integrable {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) :
    Integrable (fun u => ‖f u‖ ^ 2) := by
  obtain ⟨S, rfl⟩ := hf
  exact (S.memLp ((2 : ℕ) : ENNReal) volume).integrable_norm_pow two_ne_zero

end SchwartzDifferenceQuotient

open SchwartzDifferenceQuotient in
/- English proof (translation)
Introduce `m n T κ hκ hTS hTsub hTsmul hTiso G G' E' s hG hG' hE' hL2 hpt`. Establish `hD : ∀ h : ℝ, IsSch (fun u => (G (s + h) u - G s u) / (h : ℂ) - G' u)`. Introduce `h`. Establish `h3` using `isSch_sub (isSch_smul ((h : ℂ)⁻¹) (isSch_sub (hG (s + h)) (hG s))) hG'`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `u`. Simplify using `only [Pi.sub_apply]`. Apply the tactic sequence `try ring`. Establish `hTD : ∀ h : ℝ, T (fun u => (G (s + h) u - G s u) / (h : ℂ) - G' u) = fun u => (T (G (s + h)) u - T (G s) u) / (h : ℂ) - T G' u`. Introduce `h`.

Establish `e1 : (fun u => (G (s + h) u - G s u) / (h : ℂ) - G' u) = (fun u => (h : ℂ)⁻¹ * (G (s + h) - G s) u) - G'`. Use function extensionality and compare the values at `u`. Simplify using `only [Pi.sub_apply]`. Apply the tactic sequence `try ring`. Rewrite using `[e1, hTsub _ _ (isSch_smul _ (isSch_sub (hG _) (hG _))) hG', hTsmul _ _ (isSch_sub (hG _) (hG _)), hTsub _ _ (hG _) (hG _)]`.

Use function extensionality and compare the values at `u`. Simplify using `only [Pi.sub_apply]`. Apply the tactic sequence `try ring`. Take `⟨F, hF⟩ : ∃ F : ℝ → (Fin m → Fin n → ℂ) → ENNReal, F = fun h u => ENNReal.ofReal (‖(T (G (s + h)) u - T (G s) u) / (h : ℂ) - T G' u‖ ^ 2)` from `⟨_, rfl⟩`. Establish `hmeas : ∀ h, Measurable (F h)`.

Introduce `h`. Establish `hc` using `isSch_continuous (hTS _ (hD h))`. Rewrite `hc` using `[hTD]`. Rewrite using `[hF]`. Conclude with `ENNReal.measurable_ofReal.comp (hc.norm.pow 2).measurable`.

Establish `hlim_pt : ∀ u, Tendsto (fun h => F h u) (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (‖E' u - T G' u‖ ^ 2)))`. Introduce `u`. Rewrite using `[hF]`. Establish `h1` using `((hpt u).sub_const (T G' u)).norm.pow 2`. Conclude with `(ENNReal.continuous_ofReal.tendsto _).comp h1`.

Establish `hint : ∀ h, ∫⁻ u, F h u = ENNReal.ofReal (κ * ∫ u, ‖(G (s + h) u - G s u) / (h : ℂ) - G' u‖ ^ 2)`. Introduce `h`. Rewrite using `[← hTiso _ (hD h), hTD, ofReal_integral_eq_lintegral_ofReal, hF]`. Establish `hi` using `isSch_sq_integrable (hTS _ (hD h))`. Rewrite `hi` using `[hTD]`.

Conclude with `hi`. Conclude with `Filter.Eventually.of_forall fun u => sq_nonneg _`. Establish `hlim_int : Tendsto (fun h => ∫⁻ u, F h u) (𝓝[≠] 0) (𝓝 0)`. Repeatedly rewrite using `[hint]`. Establish `h1` using `hL2.const_mul κ`.

Rewrite `h1` using `[mul_zero]`. Establish `h2` using `(ENNReal.continuous_ofReal.tendsto 0).comp h1`. Rewrite `h2` using `[ENNReal.ofReal_zero]`. Conclude with `h2`. Establish `hfatou` using `lintegral_liminf_le (μ := (volume : Measure (Fin m → Fin n → ℂ))) (u := 𝓝[≠] (0 : ℝ)) hmeas`.

Rewrite `hfatou` using `[hlim_int.liminf_eq]`. Establish `hz : ∫⁻ u, ENNReal.ofReal (‖E' u - T G' u‖ ^ 2) = 0`. Use `le_antisymm ?_ (by simp)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Use function extensionality and compare the values at `u`. Conclude with `((hlim_pt u).liminf_eq).symm`. Use `_ ≤ 0 := hfatou`. Establish `hcT` using `isSch_continuous (hTS _ hG')`. Establish `hcE : Continuous fun u => E' u - T G' u` using `hE'.sub hcT`.

Establish `hm : Measurable fun u => ENNReal.ofReal (‖E' u - T G' u‖ ^ 2)` using `ENNReal.measurable_ofReal.comp (hcE.norm.pow 2).measurable`. Rewrite `hz` using `[lintegral_eq_zero_iff hm]`. Establish `hae : E' =ᵐ[volume] T G'` using `by filter_upwards [hz] with u hu`. Simplify using `only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hu`. Conclude with `sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm hu (sq_nonneg _))))`.

Conclude with `((Continuous.ae_eq_iff_eq volume hE' hcT).mp hae).symm`.
-/
theorem dL2 : DifferenceQuotientIsometryExchange := by
  intro m n T κ hκ hTS hTsub hTsmul hTiso G G' E' s hG hG' hE' hL2 hpt
  have hD : ∀ h : ℝ, IsSch (fun u => (G (s + h) u - G s u) / (h : ℂ) - G' u) := by
    intro h
    have h3 := isSch_sub (isSch_smul ((h : ℂ)⁻¹) (isSch_sub (hG (s + h)) (hG s))) hG'
    convert h3 using 1
    funext u
    simp only [Pi.sub_apply]
    try ring
  have hTD : ∀ h : ℝ, T (fun u => (G (s + h) u - G s u) / (h : ℂ) - G' u) =
      fun u => (T (G (s + h)) u - T (G s) u) / (h : ℂ) - T G' u := by
    intro h
    have e1 : (fun u => (G (s + h) u - G s u) / (h : ℂ) - G' u) =
        (fun u => (h : ℂ)⁻¹ * (G (s + h) - G s) u) - G' := by
      funext u
      simp only [Pi.sub_apply]
      try ring
    rw [e1, hTsub _ _ (isSch_smul _ (isSch_sub (hG _) (hG _))) hG',
      hTsmul _ _ (isSch_sub (hG _) (hG _)), hTsub _ _ (hG _) (hG _)]
    funext u
    simp only [Pi.sub_apply]
    try ring
  obtain ⟨F, hF⟩ : ∃ F : ℝ → (Fin m → Fin n → ℂ) → ENNReal,
      F = fun h u => ENNReal.ofReal (‖(T (G (s + h)) u - T (G s) u) / (h : ℂ) - T G' u‖ ^ 2) := ⟨_, rfl⟩
  have hmeas : ∀ h, Measurable (F h) := by
    intro h
    have hc := isSch_continuous (hTS _ (hD h))
    rw [hTD] at hc
    rw [hF]
    exact ENNReal.measurable_ofReal.comp (hc.norm.pow 2).measurable
  have hlim_pt : ∀ u, Tendsto (fun h => F h u) (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (‖E' u - T G' u‖ ^ 2))) := by
    intro u
    rw [hF]
    have h1 := ((hpt u).sub_const (T G' u)).norm.pow 2
    exact (ENNReal.continuous_ofReal.tendsto _).comp h1
  have hint : ∀ h, ∫⁻ u, F h u = ENNReal.ofReal (κ * ∫ u, ‖(G (s + h) u - G s u) / (h : ℂ) - G' u‖ ^ 2) := by
    intro h
    rw [← hTiso _ (hD h), hTD, ofReal_integral_eq_lintegral_ofReal, hF]
    · have hi := isSch_sq_integrable (hTS _ (hD h))
      rw [hTD] at hi
      exact hi
    · exact Filter.Eventually.of_forall fun u => sq_nonneg _
  have hlim_int : Tendsto (fun h => ∫⁻ u, F h u) (𝓝[≠] 0) (𝓝 0) := by
    simp_rw [hint]
    have h1 := hL2.const_mul κ
    rw [mul_zero] at h1
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    rw [ENNReal.ofReal_zero] at h2
    exact h2
  have hfatou := lintegral_liminf_le (μ := (volume : Measure (Fin m → Fin n → ℂ))) (u := 𝓝[≠] (0 : ℝ)) hmeas
  rw [hlim_int.liminf_eq] at hfatou
  have hz : ∫⁻ u, ENNReal.ofReal (‖E' u - T G' u‖ ^ 2) = 0 := by
    refine le_antisymm ?_ (by simp)
    calc _ = ∫⁻ u, liminf (fun h => F h u) (𝓝[≠] (0 : ℝ)) := by
          congr 1
          funext u
          exact ((hlim_pt u).liminf_eq).symm
      _ ≤ 0 := hfatou
  have hcT := isSch_continuous (hTS _ hG')
  have hcE : Continuous fun u => E' u - T G' u := hE'.sub hcT
  have hm : Measurable fun u => ENNReal.ofReal (‖E' u - T G' u‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (hcE.norm.pow 2).measurable
  rw [lintegral_eq_zero_iff hm] at hz
  have hae : E' =ᵐ[volume] T G' := by
    filter_upwards [hz] with u hu
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hu
    exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm hu (sq_nonneg _))))
  exact ((Continuous.ae_eq_iff_eq volume hE' hcT).mp hae).symm

end PositivityTheory.Rg.Sw.Glob
