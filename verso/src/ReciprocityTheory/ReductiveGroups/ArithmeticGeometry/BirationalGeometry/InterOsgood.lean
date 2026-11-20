import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

namespace ReciprocityTheory.ChartRestriction.G.Geo

def OsgoodStatement : Prop :=
  ∀ (e : ℕ) (U : Set (Fin e → ℂ)) (f : (Fin e → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f U →
    AnalyticOnNhd ℂ f U

/- English proof (translation)
Introduce `e U f hU hf z₀ hz₀`. Take `⟨r, hr, hball⟩` from `Metric.isOpen_iff.1 hU z₀ hz₀`. Establish `hs : 0 < r / 2` using `half_pos hr`. Establish `hcl : Metric.closedBall z₀ (r / 2) ⊆ U` using `(Metric.closedBall_subset_ball (half_lt_self hr)).trans hball`. Establish `hd : ∀ ζ ∈ Metric.closedBall z₀ (r / 2), DifferentiableAt ℂ f ζ` using `fun ζ hζ => hf.differentiableAt (hU.mem_nhds (hcl hζ))`.

Use `set L := ReciprocityTheory.AnForm.Osgood.fctlCLM z₀ hs f hd`. Establish `hg : AnalyticAt ℂ (fun z => ((2 * (Real.pi : ℂ) * Complex.I) ^ e)⁻¹ * L (ReciprocityTheory.AnForm.Osgood.kern z₀ (r / 2) z)) z₀` using `analyticAt_const.mul ((L.analyticAt _).comp (ReciprocityTheory.AnForm.Osgood.kern_analyticAt z₀ hs))`. Use `hg.congr ?_` and prove the remaining obligations. Use `filter_upwards [Metric.ball_mem_nhds z₀ hs] with z hz`. Rewrite using `[ReciprocityTheory.AnForm.Osgood.fctlCLM_kern hs hd hz]`.

Conclude with `inv_mul_cancel_left₀ (pow_ne_zero _ Complex.two_pi_I_ne_zero) _`.
-/
theorem osgood : OsgoodStatement := by
  intro e U f hU hf z₀ hz₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have hs : 0 < r / 2 := half_pos hr
  have hcl : Metric.closedBall z₀ (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hd : ∀ ζ ∈ Metric.closedBall z₀ (r / 2), DifferentiableAt ℂ f ζ :=
    fun ζ hζ => hf.differentiableAt (hU.mem_nhds (hcl hζ))
  set L := ReciprocityTheory.AnForm.Osgood.fctlCLM z₀ hs f hd
  have hg : AnalyticAt ℂ (fun z => ((2 * (Real.pi : ℂ) * Complex.I) ^ e)⁻¹ *
      L (ReciprocityTheory.AnForm.Osgood.kern z₀ (r / 2) z)) z₀ :=
    analyticAt_const.mul ((L.analyticAt _).comp (ReciprocityTheory.AnForm.Osgood.kern_analyticAt z₀ hs))
  refine hg.congr ?_
  filter_upwards [Metric.ball_mem_nhds z₀ hs] with z hz
  rw [ReciprocityTheory.AnForm.Osgood.fctlCLM_kern hs hd hz]
  exact inv_mul_cancel_left₀ (pow_ne_zero _ Complex.two_pi_I_ne_zero) _

end ReciprocityTheory.ChartRestriction.G.Geo
