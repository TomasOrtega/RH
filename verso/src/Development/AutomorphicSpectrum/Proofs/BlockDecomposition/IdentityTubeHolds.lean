import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.Eis

/- English proof (translation)
Establish `hc : Continuous fun l : ℂ × ℂ => (l.1.re, l.2.re)` using `(Complex.continuous_re.comp continuous_fst).prodMk (Complex.continuous_re.comp continuous_snd)`. Conclude with `hc.isOpen_preimage Ω hΩ`.
-/
theorem tube_isOpen {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) : IsOpen (tube Ω) := by
  have hc : Continuous fun l : ℂ × ℂ => (l.1.re, l.2.re) :=
    (Complex.continuous_re.comp continuous_fst).prodMk (Complex.continuous_re.comp continuous_snd)
  exact hc.isOpen_preimage Ω hΩ

/- English proof (translation)
Introduce `x hx y hy a b ha hb hab`. Establish `key` using `hc hx hy ha hb hab`. Simplify using `only [tube, Set.mem_ofPred_eq] at hx hy key ⊢`. Use `key using 1` and compare the differences between its conclusion and the goal. Use `ext`.

Simplify using `only [Prod.fst_add, Prod.smul_fst, Complex.add_re, smul_eq_mul, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Prod.fst_add, Prod.smul_mk, Prod.mk_add_mk]`. Take the linear combination `(-p.1.re) * hab`. Simplify using `only [Prod.snd_add, Prod.smul_snd, Complex.add_re, smul_eq_mul, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Prod.smul_mk, Prod.mk_add_mk]`. Take the linear combination `(-p.2.re) * hab`.
-/
theorem line_tube_convex {Ω : Set (ℝ × ℝ)} (hc : Convex ℝ Ω) (p v : ℂ × ℂ) :
    Convex ℝ {τ : ℂ | p + τ • v ∈ tube Ω} := by
  intro x hx y hy a b ha hb hab
  have key := hc hx hy ha hb hab
  simp only [tube, Set.mem_ofPred_eq] at hx hy key ⊢
  convert key using 1
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, Complex.add_re, smul_eq_mul, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Prod.fst_add, Prod.smul_mk, Prod.mk_add_mk]
    linear_combination (-p.1.re) * hab
  · simp only [Prod.snd_add, Prod.smul_snd, Complex.add_re, smul_eq_mul, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Prod.smul_mk, Prod.mk_add_mk]
    linear_combination (-p.2.re) * hab

/- English proof (translation)
Introduce `X _ _ _ Ω Ω' F F' hΩ hc hΩ' hne hsub hF hF' heq z hz`. Take `⟨ω, hω⟩` from `hne`. Use `set z0 : ℂ × ℂ := ((ω.1 : ℂ), (ω.2 : ℂ)) with hz0`. Establish `hz0' : z0 ∈ tube Ω'` using `by simpa [tube, hz0] using hω`. Establish `hline : Continuous fun τ : ℂ => z0 + τ • (z - z0)` using `by fun_prop`.

Establish `hDo : IsOpen {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω}` using `(tube_isOpen hΩ).preimage hline`. Establish `hDc : Convex ℝ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω}` using `line_tube_convex hc z0 (z - z0)`. Establish `h0 : (0 : ℂ) ∈ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω}` using `by show z0 + (0 : ℂ) • (z - z0) ∈ tube Ω`. Rewrite using `[zero_smul, add_zero]`. Conclude with `hsub hz0'`.

Establish `h1 : (1 : ℂ) ∈ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω}` using `by simpa using hz`. Establish `hA` using `(hF z0 (z - z0)).analyticOnNhd hDo`. Establish `hA'` using `(hF' z0 (z - z0)).analyticOnNhd hDo`. Establish `hev : (fun τ : ℂ => F (z0 + τ • (z - z0))) =ᶠ[𝓝 0] (fun τ : ℂ => F' (z0 + τ • (z - z0)))`. Establish `hO' : IsOpen {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω'}` using `(tube_isOpen hΩ').preimage hline`.

Use `filter_upwards [hO'.mem_nhds (by simpa using hz0')] with τ hτ`. Conclude with `heq hτ`. Use `hA.eqOn_of_preconnected_of_eventuallyEq hA' hDc.isPreconnected h0 hev h1` as an intermediate fact. Simplify using `using this`.
-/
theorem idTube : IdTube := by
  intro X _ _ _ Ω Ω' F F' hΩ hc hΩ' hne hsub hF hF' heq z hz
  obtain ⟨ω, hω⟩ := hne
  set z0 : ℂ × ℂ := ((ω.1 : ℂ), (ω.2 : ℂ)) with hz0
  have hz0' : z0 ∈ tube Ω' := by simpa [tube, hz0] using hω
  have hline : Continuous fun τ : ℂ => z0 + τ • (z - z0) := by fun_prop
  have hDo : IsOpen {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := (tube_isOpen hΩ).preimage hline
  have hDc : Convex ℝ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := line_tube_convex hc z0 (z - z0)
  have h0 : (0 : ℂ) ∈ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := by
    show z0 + (0 : ℂ) • (z - z0) ∈ tube Ω
    rw [zero_smul, add_zero]
    exact hsub hz0'
  have h1 : (1 : ℂ) ∈ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := by simpa using hz
  have hA := (hF z0 (z - z0)).analyticOnNhd hDo
  have hA' := (hF' z0 (z - z0)).analyticOnNhd hDo
  have hev : (fun τ : ℂ => F (z0 + τ • (z - z0))) =ᶠ[𝓝 0] (fun τ : ℂ => F' (z0 + τ • (z - z0))) := by
    have hO' : IsOpen {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω'} := (tube_isOpen hΩ').preimage hline
    filter_upwards [hO'.mem_nhds (by simpa using hz0')] with τ hτ
    exact heq hτ
  have := hA.eqOn_of_preconnected_of_eventuallyEq hA' hDc.isPreconnected h0 hev h1
  simpa using this

end GlobalTheory.CompanionTheory.Eis
