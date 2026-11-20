import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotStage

open MeasureTheory Topology
open scoped ENNReal

/- English proof (translation)
Introduce `hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ G' _ _ _ _ _ _ _ _ T' _ _ _ _ _ _ _ _ μ j ν hP μ' j' ν' hP' e y hμ hν F hF hinv`. Take `⟨ρ0, -, hρ, -⟩` from `hN G' T' μ' j' ν' hP'`. Use `set ρ : G' → ℝ≥0∞ := fun g => (ρ0 g : ℝ≥0∞) with hρdef`. Establish `hjc : Continuous j` using `hP.2.1.continuous`. Establish `hj'c : Continuous j'` using `hP'.2.1.continuous`.

Establish `hec : Continuous e` using `e.continuous_toFun`. Establish `hejc : Continuous (fun t => e (j t))` using `hec.comp hjc`. Use `haveI := hP.2.2.1`. Use `haveI := hP'.1.1`. Use `haveI := hP'.1.2`.

Establish `hrange : ∀ t, e (j t) ∈ Set.range j'`. Establish `hcl : IsClosed (Set.range j')` using `hP'.2.1.isClosed_range`. Establish `ho : IsOpen (Set.range j')ᶜ` using `hcl.isOpen_compl`. Establish `h0 : (ν.map (fun t => e (j t))) (Set.range j')ᶜ = 0`. Rewrite using `[hν, Measure.map_apply hj'c.measurable ho.measurableSet]`.

Establish `: j' ⁻¹' (Set.range j')ᶜ = ∅`. Use extensionality with `t`. Simplify using the standard rewrite rules. Rewrite using `[this, measure_empty]`. Rewrite `h0` using `[Measure.map_apply hejc.measurable ho.measurableSet]`.

Establish `he` using `(ho.preimage hejc).eq_empty_of_measure_zero h0`. Introduce `t`. Assume the negation of the conclusion as `hc`. Establish `: t ∈ (fun t => e (j t)) ⁻¹' (Set.range j')ᶜ` using `hc`. Rewrite `this` using `[he]`.

Conclude with `this`. Establish `hφ : Measurable (fun g : G => e g * y)` using `(hec.mul continuous_const).measurable`. Establish `hF1 : Measurable (fun g => F (e g * y))` using `hF.comp hφ`. Establish `hinv1 : ∀ t g, (fun g => F (e g * y)) (j t * g) = (fun g => F (e g * y)) g`. Introduce `t g`.

Take `⟨t', ht'⟩` from `hrange t`. Simplify using `only [map_mul, ← ht', mul_assoc, hinv]`. Establish `hρ1 : UpperTheory.ConvolutionTheory.G.IsNrm j ν (fun g => ρ (e g * y))`. Use `⟨hρ.1.comp hφ, fun x => ?_⟩` and prove the remaining obligations. Establish `hm : Measurable (fun z : G' => ρ (z * (e x * y)))` using `hρ.1.comp (measurable_mul_const _)`.

Establish `h1` using `lintegral_map (μ := ν) hm hejc.measurable`. Establish `h2` using `lintegral_map (μ := ν') hm hj'c.measurable`. Rewrite `h1` using `[hν, h2, hρ.2]`. Simplify using `only [map_mul, mul_assoc]`. Conclude with `h1.symm`.

Use `haveI : μ'.IsMulRightInvariant := by`. Establish `h : μ'.inv.IsMulRightInvariant` using `inferInstance`. Rewrite `h` using `[Measure.inv_eq_self]`. Then use the resulting hypothesis. Establish `hmp : MeasurePreserving (fun g : G => e g * y) μ μ'` using `(measurePreserving_mul_right μ' y).comp ⟨hec.measurable, hμ⟩`. Establish `hemb : MeasurableEmbedding (fun g : G => e g * y)` using `(e.toHomeomorph.trans (Homeomorph.mulRight y)).measurableEmbedding`.

Take `⟨a1, -, a3⟩` from `hE G T μ j ν hP _ hF1 hinv1 _ hρ1`. Take `⟨b1, -, b3⟩` from `hE G' T' μ' j' ν' hP' F hF hinv ρ hρ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[a1, b1]`. Conclude with `hmp.integrable_comp_emb hemb (g := fun x => F x * ((ρ x).toReal : ℂ))`.

Rewrite using `[a3, b3]`. Conclude with `hmp.integral_comp hemb (fun x => F x * ((ρ x).toReal : ℂ))`.
-/
theorem UpperTheory.ConvolutionTheory.G.quotMap_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotMap := by
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ G' _ _ _ _ _ _ _ _ T' _ _ _ _ _ _ _ _
    μ j ν hP μ' j' ν' hP' e y hμ hν F hF hinv
  obtain ⟨ρ0, -, hρ, -⟩ := hN G' T' μ' j' ν' hP'
  set ρ : G' → ℝ≥0∞ := fun g => (ρ0 g : ℝ≥0∞) with hρdef
  have hjc : Continuous j := hP.2.1.continuous
  have hj'c : Continuous j' := hP'.2.1.continuous
  have hec : Continuous e := e.continuous_toFun
  have hejc : Continuous (fun t => e (j t)) := hec.comp hjc
  haveI := hP.2.2.1
  haveI := hP'.1.1
  haveI := hP'.1.2
  have hrange : ∀ t, e (j t) ∈ Set.range j' := by
    have hcl : IsClosed (Set.range j') := hP'.2.1.isClosed_range
    have ho : IsOpen (Set.range j')ᶜ := hcl.isOpen_compl
    have h0 : (ν.map (fun t => e (j t))) (Set.range j')ᶜ = 0 := by
      rw [hν, Measure.map_apply hj'c.measurable ho.measurableSet]
      have : j' ⁻¹' (Set.range j')ᶜ = ∅ := by
        ext t; simp
      rw [this, measure_empty]
    rw [Measure.map_apply hejc.measurable ho.measurableSet] at h0
    have he := (ho.preimage hejc).eq_empty_of_measure_zero h0
    intro t
    by_contra hc
    have : t ∈ (fun t => e (j t)) ⁻¹' (Set.range j')ᶜ := hc
    rw [he] at this
    exact this
  have hφ : Measurable (fun g : G => e g * y) := (hec.mul continuous_const).measurable
  have hF1 : Measurable (fun g => F (e g * y)) := hF.comp hφ
  have hinv1 : ∀ t g, (fun g => F (e g * y)) (j t * g) = (fun g => F (e g * y)) g := by
    intro t g
    obtain ⟨t', ht'⟩ := hrange t
    simp only [map_mul, ← ht', mul_assoc, hinv]
  have hρ1 : UpperTheory.ConvolutionTheory.G.IsNrm j ν (fun g => ρ (e g * y)) := by
    refine ⟨hρ.1.comp hφ, fun x => ?_⟩
    have hm : Measurable (fun z : G' => ρ (z * (e x * y))) := hρ.1.comp (measurable_mul_const _)
    have h1 := lintegral_map (μ := ν) hm hejc.measurable
    have h2 := lintegral_map (μ := ν') hm hj'c.measurable
    rw [hν, h2, hρ.2] at h1
    simp only [map_mul, mul_assoc]
    exact h1.symm
  haveI : μ'.IsMulRightInvariant := by
    have h : μ'.inv.IsMulRightInvariant := inferInstance
    rwa [Measure.inv_eq_self] at h
  have hmp : MeasurePreserving (fun g : G => e g * y) μ μ' :=
    (measurePreserving_mul_right μ' y).comp ⟨hec.measurable, hμ⟩
  have hemb : MeasurableEmbedding (fun g : G => e g * y) :=
    (e.toHomeomorph.trans (Homeomorph.mulRight y)).measurableEmbedding
  obtain ⟨a1, -, a3⟩ := hE G T μ j ν hP _ hF1 hinv1 _ hρ1
  obtain ⟨b1, -, b3⟩ := hE G' T' μ' j' ν' hP' F hF hinv ρ hρ
  refine ⟨?_, ?_⟩
  · rw [a1, b1]
    exact hmp.integrable_comp_emb hemb (g := fun x => F x * ((ρ x).toReal : ℂ))
  · rw [a3, b3]
    exact hmp.integral_comp hemb (fun x => F x * ((ρ x).toReal : ℂ))
