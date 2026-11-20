import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotStage

open MeasureTheory Topology
open scoped ENNReal

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Take `⟨h1', h2'⟩` from `h'`. Use `⟨inferInstance, ⟨?_⟩⟩` and prove the remaining obligations. Establish `e : (Inv.inv : G × G' → G × G') = Prod.map Inv.inv Inv.inv` using `rfl`. Rewrite using `[Measure.inv_def, e, ← Measure.map_prod_map _ _ measurable_inv measurable_inv, Measure.map_inv_eq_self, Measure.map_inv_eq_self]`.
-/
private theorem UpperTheory.ConvolutionTheory.G.uni_prod {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    [LocallyCompactSpace G'] [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G']
    {μ : Measure G} {μ' : Measure G'} (h : UpperTheory.ConvolutionTheory.G.Uni μ) (h' : UpperTheory.ConvolutionTheory.G.Uni μ') :
    UpperTheory.ConvolutionTheory.G.Uni (μ.prod μ') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨inferInstance, ⟨?_⟩⟩
  have e : (Inv.inv : G × G' → G × G') = Prod.map Inv.inv Inv.inv := rfl
  rw [Measure.inv_def, e, ← Measure.map_prod_map _ _ measurable_inv measurable_inv,
    Measure.map_inv_eq_self, Measure.map_inv_eq_self]

/- English proof (translation)
Introduce `hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ G' _ _ _ _ _ _ _ _ T' _ _ _ _ _ _ _ _ μ j ν hP μ' j' ν' hP'`. Establish `hPP : UpperTheory.ConvolutionTheory.G.Pair (μ.prod μ') (j.prodMap j') (ν.prod ν')` using `⟨UpperTheory.ConvolutionTheory.G.uni_prod hP.1 hP'.1, hP.2.1.prodMap hP'.2.1, UpperTheory.ConvolutionTheory.G.uni_prod hP.2.2 hP'.2.2⟩`. Use `⟨hPP, fun F F' hF hFi hF' hFi' => ?_⟩` and prove the remaining obligations. Take `⟨ρ, hc, hρ, -⟩` from `hN G T μ j ν hP`. Take `⟨ρ', hc', hρ', -⟩` from `hN G' T' μ' j' ν' hP'`.

Use `haveI := hP.1.1`. Use `haveI := hP'.1.1`. Use `haveI := hP.2.2.1`. Use `haveI := hP'.2.2.1`. Establish `hj : Measurable j` using `hP.2.1.continuous.measurable`.

Establish `hj' : Measurable j'` using `hP'.2.1.continuous.measurable`. Establish `hρρ : UpperTheory.ConvolutionTheory.G.IsNrm (j.prodMap j') (ν.prod ν') (fun g : G × G' => (ρ g.1 : ℝ≥0∞) * (ρ' g.2 : ℝ≥0∞))`. Use `⟨(hρ.1.comp measurable_fst).mul (hρ'.1.comp measurable_snd), fun x => ?_⟩` and prove the remaining obligations. Use `lintegral_prod_mul (μ := ν) (ν := ν') (f := fun t => (ρ (j t * x.1) : ℝ≥0∞)) (g := fun t => (ρ' (j' t * x.2) : ℝ≥0∞)) (hρ.1.comp (hj.mul_const _)).aemeasurable (hρ'.1.comp (hj'.mul_const _)).aemeasurable` as an intermediate fact. Rewrite `this` using `[hρ.2 x.1, hρ'.2 x.2, mul_one]`.

Conclude with `this`. Establish `hm : Measurable (fun g : G × G' => F g.1 * F' g.2)` using `(hF.comp measurable_fst).mul (hF'.comp measurable_snd)`. Establish `hi : ∀ (t : T × T') (g : G × G'), (fun g : G × G' => F g.1 * F' g.2) (j.prodMap j' t * g) = (fun g : G × G' => F g.1 * F' g.2) g`. Introduce `t g`. Use `show F (j t.1 * g.1) * F' (j' t.2 * g.2) = _`.

Rewrite using `[hFi, hFi']`. Take `⟨a1, -, a3⟩` from `hE G T μ j ν hP F hF hFi _ hρ`. Take `⟨b1, -, b3⟩` from `hE G' T' μ' j' ν' hP' F' hF' hFi' _ hρ'`. Take `⟨c1, -, c3⟩` from `hE (G × G') (T × T') _ _ _ hPP _ hm hi _ hρρ`. Establish `key : (fun x : G × G' => F x.1 * F' x.2 * ((((ρ x.1 : ℝ≥0∞) * (ρ' x.2 : ℝ≥0∞)).toReal : ℝ) : ℂ)) = fun x : G × G' => (F x.1 * (((ρ x.1 : ℝ≥0∞).toReal : ℝ) : ℂ)) * (F' x.2 * (((ρ' x.2 : ℝ≥0∞).toReal : ℝ) : ℂ))`.

Use function extensionality and compare the values at `x`. Rewrite using `[ENNReal.toReal_mul, Complex.ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun h h' => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[c1, key]`.

Conclude with `(a1.1 h).mul_prod (b1.1 h')`. Rewrite using `[c3, key, a3, b3]`. Conclude with `integral_prod_mul (fun x => F x * (((ρ x : ℝ≥0∞).toReal : ℝ) : ℂ)) (fun x => F' x * (((ρ' x : ℝ≥0∞).toReal : ℝ) : ℂ))`.
-/
theorem UpperTheory.ConvolutionTheory.G.quotProd_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotProd := by
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ G' _ _ _ _ _ _ _ _ T' _ _ _ _ _ _ _ _
    μ j ν hP μ' j' ν' hP'
  have hPP : UpperTheory.ConvolutionTheory.G.Pair (μ.prod μ') (j.prodMap j') (ν.prod ν') :=
    ⟨UpperTheory.ConvolutionTheory.G.uni_prod hP.1 hP'.1, hP.2.1.prodMap hP'.2.1, UpperTheory.ConvolutionTheory.G.uni_prod hP.2.2 hP'.2.2⟩
  refine ⟨hPP, fun F F' hF hFi hF' hFi' => ?_⟩
  obtain ⟨ρ, hc, hρ, -⟩ := hN G T μ j ν hP
  obtain ⟨ρ', hc', hρ', -⟩ := hN G' T' μ' j' ν' hP'
  haveI := hP.1.1
  haveI := hP'.1.1
  haveI := hP.2.2.1
  haveI := hP'.2.2.1
  have hj : Measurable j := hP.2.1.continuous.measurable
  have hj' : Measurable j' := hP'.2.1.continuous.measurable
  have hρρ : UpperTheory.ConvolutionTheory.G.IsNrm (j.prodMap j') (ν.prod ν')
      (fun g : G × G' => (ρ g.1 : ℝ≥0∞) * (ρ' g.2 : ℝ≥0∞)) := by
    refine ⟨(hρ.1.comp measurable_fst).mul (hρ'.1.comp measurable_snd), fun x => ?_⟩
    have := lintegral_prod_mul (μ := ν) (ν := ν') (f := fun t => (ρ (j t * x.1) : ℝ≥0∞))
      (g := fun t => (ρ' (j' t * x.2) : ℝ≥0∞))
      (hρ.1.comp (hj.mul_const _)).aemeasurable (hρ'.1.comp (hj'.mul_const _)).aemeasurable
    rw [hρ.2 x.1, hρ'.2 x.2, mul_one] at this
    exact this
  have hm : Measurable (fun g : G × G' => F g.1 * F' g.2) :=
    (hF.comp measurable_fst).mul (hF'.comp measurable_snd)
  have hi : ∀ (t : T × T') (g : G × G'),
      (fun g : G × G' => F g.1 * F' g.2) (j.prodMap j' t * g) = (fun g : G × G' => F g.1 * F' g.2) g := by
    intro t g
    show F (j t.1 * g.1) * F' (j' t.2 * g.2) = _
    rw [hFi, hFi']
  obtain ⟨a1, -, a3⟩ := hE G T μ j ν hP F hF hFi _ hρ
  obtain ⟨b1, -, b3⟩ := hE G' T' μ' j' ν' hP' F' hF' hFi' _ hρ'
  obtain ⟨c1, -, c3⟩ := hE (G × G') (T × T') _ _ _ hPP _ hm hi _ hρρ
  have key : (fun x : G × G' => F x.1 * F' x.2 * ((((ρ x.1 : ℝ≥0∞) * (ρ' x.2 : ℝ≥0∞)).toReal : ℝ) : ℂ)) =
      fun x : G × G' => (F x.1 * (((ρ x.1 : ℝ≥0∞).toReal : ℝ) : ℂ)) * (F' x.2 * (((ρ' x.2 : ℝ≥0∞).toReal : ℝ) : ℂ)) := by
    funext x
    rw [ENNReal.toReal_mul, Complex.ofReal_mul]
    ring
  refine ⟨fun h h' => ?_, ?_⟩
  · rw [c1, key]
    exact (a1.1 h).mul_prod (b1.1 h')
  · rw [c3, key, a3, b3]
    exact integral_prod_mul (fun x => F x * (((ρ x : ℝ≥0∞).toReal : ℝ) : ℂ))
      (fun x => F' x * (((ρ' x : ℝ≥0∞).toReal : ℝ) : ℂ))
