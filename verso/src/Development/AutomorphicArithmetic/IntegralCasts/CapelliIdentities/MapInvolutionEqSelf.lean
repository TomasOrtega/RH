import Mathlib

/- English proof (translation)
Introduce `X _ μ _ ι c hι hinv hc`. Distinguish the cases in `h0 : μ = 0`. Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Establish `h1 : (μ.map ι).map ι = μ`.

Rewrite using `[MeasureTheory.Measure.map_map hι hι]`. Establish `h : (ι ∘ ι) =ᵐ[μ] id` using `hinv`. Rewrite using `[MeasureTheory.Measure.map_congr h, MeasureTheory.Measure.map_id]`. Establish `h2 : (c * c) • μ = μ`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨s, -, -, hs0, hs1⟩` from `MeasureTheory.Measure.exists_subset_measure_lt_top (μ := μ) (s := Set.univ) (r := 0) MeasurableSet.univ (MeasureTheory.Measure.measure_univ_pos.mpr h0)`. Establish `h3 : ((c * c : NNReal) : ENNReal) * μ s = 1 * μ s`. Establish `h` using `congrArg (fun ν : MeasureTheory.Measure X => ν s) h2`. Simplify `h` using `[ENNReal.smul_def]`. Establish `h4 : ((c * c : NNReal) : ENNReal) = 1` using `(ENNReal.mul_left_inj hs0.ne' hs1.ne).mp h3`.

Establish `h5 : c * c = 1` using `by exact_mod_cast h4`. Establish `h6 : c = 1`. Establish `h : (c : ℝ) * c = 1` using `by exact_mod_cast h5`. Establish `hc0 : (0 : ℝ) ≤ c` using `c.2`. Establish `h' : (c : ℝ) = 1` using `by nlinarith`.

Conclude with `h'` after adjusting the coercions. Rewrite using `[hc, h6, one_smul]`.
-/
theorem UpperTheory.map_involution_eq_self :
    ∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ] (ι : X → X) (c : NNReal), Measurable ι → (∀ᵐ x ∂μ, ι (ι x) = x) → μ.map ι = c • μ → μ.map ι = μ := by
  intro X _ μ _ ι c hι hinv hc
  by_cases h0 : μ = 0
  · subst h0
    simp
  have h1 : (μ.map ι).map ι = μ := by
    rw [MeasureTheory.Measure.map_map hι hι]
    have h : (ι ∘ ι) =ᵐ[μ] id := hinv
    rw [MeasureTheory.Measure.map_congr h, MeasureTheory.Measure.map_id]
  have h2 : (c * c) • μ = μ := by
    calc (c * c) • μ = c • (c • μ) := mul_smul c c μ
      _ = c • μ.map ι := by rw [hc]
      _ = (c • μ).map ι := (MeasureTheory.Measure.map_smul c μ ι).symm
      _ = (μ.map ι).map ι := by rw [hc]
      _ = μ := h1
  obtain ⟨s, -, -, hs0, hs1⟩ :=
    MeasureTheory.Measure.exists_subset_measure_lt_top (μ := μ) (s := Set.univ) (r := 0)
      MeasurableSet.univ (MeasureTheory.Measure.measure_univ_pos.mpr h0)
  have h3 : ((c * c : NNReal) : ENNReal) * μ s = 1 * μ s := by
    have h := congrArg (fun ν : MeasureTheory.Measure X => ν s) h2
    simpa [ENNReal.smul_def] using h
  have h4 : ((c * c : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj hs0.ne' hs1.ne).mp h3
  have h5 : c * c = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have h : (c : ℝ) * c = 1 := by exact_mod_cast h5
    have hc0 : (0 : ℝ) ≤ c := c.2
    have h' : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast h'
  rw [hc, h6, one_smul]
