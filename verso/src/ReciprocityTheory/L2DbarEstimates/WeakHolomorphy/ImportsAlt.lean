import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

/- English proof (translation)
Introduce `n Ω F a hΩ hc hF ha h0 x hx`. Use `set L : ℂ → V n := fun t => a + t • (x - a) with hL`. Establish `hLd : Differentiable ℂ L` using `(differentiable_const a).add (differentiable_id.smul_const (x - a))`. Establish `hLc : Continuous L` using `hLd.continuous`. Use `set U : Set ℂ := L ⁻¹' Ω with hU`.

Establish `hUo : IsOpen U` using `hΩ.preimage hLc`. Establish `hUconv : Convex ℝ U`. Introduce `t1 ht1 t2 ht2 s1 s2 hs1 hs2 hs`. Use `show L (s1 • t1 + s2 • t2) ∈ Ω`. Establish `key : L (s1 • t1 + s2 • t2) = s1 • L t1 + s2 • L t2`.

Establish `e : s1 • L t1 + s2 • L t2 = (s1 + s2) • a + (s1 • t1 + s2 • t2) • (x - a)`. Simplify using `only [hL, smul_add, add_smul, smul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, hs, one_smul]`. Rewrite using `[key]`.

Conclude with `hc ht1 ht2 hs1 hs2 hs`. Establish `hG : DifferentiableOn ℂ (F ∘ L) U` using `hF.comp hLd.differentiableOn (fun t ht => ht)`. Establish `hA : AnalyticOnNhd ℂ (F ∘ L) U` using `hG.analyticOnNhd hUo`. Establish `h0U : (0 : ℂ) ∈ U` using `by show L 0 ∈ Ω`. Simplify `ha` using `[hL]`.

Establish `h1U : (1 : ℂ) ∈ U` using `by show L 1 ∈ Ω`. Simplify `hx` using `[hL]`. Establish `hL0 : L 0 = a` using `by simp [hL]`. Establish `hev : F ∘ L =ᶠ[𝓝 0] 0`. Establish `ht : Filter.Tendsto L (𝓝 0) (𝓝 a)`.

Rewrite using `[← hL0]`. Conclude with `hLc.continuousAt.tendsto`. Conclude with `ht.eventually h0`. Establish `hEq` using `hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconv.isPreconnected h0U hev`. Establish `h1` using `hEq h1U`.

Simplify `h1` using `[hL]`.
-/
theorem ident : IdentStatement := by
  intro n Ω F a hΩ hc hF ha h0 x hx
  set L : ℂ → V n := fun t => a + t • (x - a) with hL
  have hLd : Differentiable ℂ L := (differentiable_const a).add (differentiable_id.smul_const (x - a))
  have hLc : Continuous L := hLd.continuous
  set U : Set ℂ := L ⁻¹' Ω with hU
  have hUo : IsOpen U := hΩ.preimage hLc
  have hUconv : Convex ℝ U := by
    intro t1 ht1 t2 ht2 s1 s2 hs1 hs2 hs
    show L (s1 • t1 + s2 • t2) ∈ Ω
    have key : L (s1 • t1 + s2 • t2) = s1 • L t1 + s2 • L t2 := by
      have e : s1 • L t1 + s2 • L t2 = (s1 + s2) • a + (s1 • t1 + s2 • t2) • (x - a) := by
        simp only [hL, smul_add, add_smul, smul_assoc]
        abel
      rw [e, hs, one_smul]
    rw [key]
    exact hc ht1 ht2 hs1 hs2 hs
  have hG : DifferentiableOn ℂ (F ∘ L) U := hF.comp hLd.differentiableOn (fun t ht => ht)
  have hA : AnalyticOnNhd ℂ (F ∘ L) U := hG.analyticOnNhd hUo
  have h0U : (0 : ℂ) ∈ U := by
    show L 0 ∈ Ω
    simpa [hL] using ha
  have h1U : (1 : ℂ) ∈ U := by
    show L 1 ∈ Ω
    simpa [hL] using hx
  have hL0 : L 0 = a := by simp [hL]
  have hev : F ∘ L =ᶠ[𝓝 0] 0 := by
    have ht : Filter.Tendsto L (𝓝 0) (𝓝 a) := by
      rw [← hL0]
      exact hLc.continuousAt.tendsto
    exact ht.eventually h0
  have hEq := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconv.isPreconnected h0U hev
  have h1 := hEq h1U
  simpa [hL] using h1

end ReciprocityTheory.L2DbarEstimates.C
