import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier.ShiftLine

/- English proof (translation)
Establish `hpt : ∀ c y : ℝ, (⟨c, y⟩ : ℂ) = (c : ℂ) + (y : ℂ) * Complex.I`. Introduce `c y`. Apply the tactic sequence `apply Complex.ext <;> simp`. Simplify using `only [hpt]`. Establish `hint : ∀ c ∈ Set.Icc a b, Integrable (fun y : ℝ => f ((c : ℂ) + (y : ℂ) * Complex.I))`.

Introduce `c hc`. Establish `hcont : Continuous fun y : ℝ => f ((c : ℂ) + (y : ℂ) * Complex.I)` using `hd.continuousOn.comp_continuous (by fun_prop) (fun y => by simpa using hc)`. Use `((integrable_exp_neg_mul_sq one_pos).const_mul M).mono' hcont.aestronglyMeasurable (ae_of_all _ fun y => ?_)` and prove the remaining obligations. Use `hb ((c : ℂ) + (y : ℂ) * Complex.I) (by simpa using hc)` as an intermediate fact. Simplify using `using this`.

Establish `hhor : ∀ s : ℝ, ‖∫ x in a..b, f ((x : ℂ) + (s : ℂ) * Complex.I)‖ ≤ M * Real.exp (-s ^ 2) * (b - a)`. Introduce `s`. Establish `h` using `intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := M * Real.exp (-s ^ 2)) (f := fun x : ℝ => f ((x : ℂ) + (s : ℂ) * Complex.I)) ?_`. Rewrite `h` using `[abs_of_nonneg (sub_nonneg.mpr hab)]`. Then use the resulting hypothesis. Introduce `x hx`.

Rewrite `hx` using `[Set.uIoc_of_le hab]`. Use `hb ((x : ℂ) + (s : ℂ) * Complex.I) (by simp; exact ⟨hx.1.le, hx.2⟩)` as an intermediate fact. Simplify using `using this`. Establish `hrect : ∀ R : ℝ, 0 ≤ R → ((∫ x in a..b, f ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)) - ∫ x in a..b, f ((x : ℂ) + (R : ℂ) * Complex.I)) + Complex.I • (∫ y in (-R)..R, f ((b : ℂ) + (y : ℂ) * Complex.I)) - Complex.I • (∫ y in (-R)..R, f ((a : ℂ) + (y : ℂ) * Complex.I)) = 0`. Introduce `R _`.

Use `Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, -R⟩ ⟨b, R⟩ ?_` and prove the remaining obligations. Use `hd.mono fun z hz => ?_` and prove the remaining obligations. Conclude with `(Set.uIcc_of_le hab).subset (Complex.mem_reProdIm.mp hz).1`. Establish `hexp : Tendsto (fun R : ℝ => Real.exp (-R ^ 2)) atTop (𝓝 0)` using `Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero))`. Establish `hH : Tendsto (fun R : ℝ => (∫ x in a..b, f ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)) - ∫ x in a..b, f ((x : ℂ) + (R : ℂ) * Complex.I)) atTop (𝓝 0)`.

Establish `hT : Tendsto (fun R : ℝ => 2 * (M * Real.exp (-R ^ 2) * (b - a))) atTop (𝓝 0)`. Simplify using `using ((hexp.const_mul M).mul_const (b - a)).const_mul 2`. Use `squeeze_zero_norm (fun R => ?_) hT` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[neg_sq]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hVa : Tendsto (fun R : ℝ => ∫ y in (-R)..R, f ((a : ℂ) + (y : ℂ) * Complex.I)) atTop (𝓝 (∫ y : ℝ, f ((a : ℂ) + (y : ℂ) * Complex.I)))` using `intervalIntegral_tendsto_integral (hint a ⟨le_rfl, hab⟩) tendsto_neg_atTop_atBot tendsto_id`. Establish `hVb : Tendsto (fun R : ℝ => ∫ y in (-R)..R, f ((b : ℂ) + (y : ℂ) * Complex.I)) atTop (𝓝 (∫ y : ℝ, f ((b : ℂ) + (y : ℂ) * Complex.I)))` using `intervalIntegral_tendsto_integral (hint b ⟨hab, le_rfl⟩) tendsto_neg_atTop_atBot tendsto_id`. Establish `hlim` using `(hH.add (hVb.const_smul Complex.I)).sub (hVa.const_smul Complex.I)`. Establish `heq : (0 : Y) + Complex.I • (∫ y : ℝ, f ((b : ℂ) + (y : ℂ) * Complex.I)) - Complex.I • (∫ y : ℝ, f ((a : ℂ) + (y : ℂ) * Complex.I)) = 0` using `tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ((eventually_ge_atTop 0).mono fun R hR => (hrect R hR).symm))`.

Rewrite `heq` using `[zero_add, ← smul_sub, smul_eq_zero]`. Break down `heq with h | h` into its components or cases. Conclude with `absurd h Complex.I_ne_zero`. Conclude with `(sub_eq_zero.mp h).symm`.
-/
theorem integral_vertical_line_eq {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (f : ℂ → Y) (a b M : ℝ) (hab : a ≤ b)
    (hd : DifferentiableOn ℂ f {z : ℂ | z.re ∈ Set.Icc a b})
    (hb : ∀ z : ℂ, z.re ∈ Set.Icc a b → ‖f z‖ ≤ M * Real.exp (-z.im ^ 2)) :
    ∫ y : ℝ, f ⟨a, y⟩ = ∫ y : ℝ, f ⟨b, y⟩ := by
  have hpt : ∀ c y : ℝ, (⟨c, y⟩ : ℂ) = (c : ℂ) + (y : ℂ) * Complex.I := by
    intro c y
    apply Complex.ext <;> simp
  simp only [hpt]
  have hint : ∀ c ∈ Set.Icc a b,
      Integrable (fun y : ℝ => f ((c : ℂ) + (y : ℂ) * Complex.I)) := by
    intro c hc
    have hcont : Continuous fun y : ℝ => f ((c : ℂ) + (y : ℂ) * Complex.I) :=
      hd.continuousOn.comp_continuous (by fun_prop) (fun y => by simpa using hc)
    refine ((integrable_exp_neg_mul_sq one_pos).const_mul M).mono' hcont.aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    have := hb ((c : ℂ) + (y : ℂ) * Complex.I) (by simpa using hc)
    simpa using this
  have hhor : ∀ s : ℝ,
      ‖∫ x in a..b, f ((x : ℂ) + (s : ℂ) * Complex.I)‖ ≤ M * Real.exp (-s ^ 2) * (b - a) := by
    intro s
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := M * Real.exp (-s ^ 2)) (f := fun x : ℝ => f ((x : ℂ) + (s : ℂ) * Complex.I)) ?_
    · rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at h
    · intro x hx
      rw [Set.uIoc_of_le hab] at hx
      have := hb ((x : ℂ) + (s : ℂ) * Complex.I) (by simp; exact ⟨hx.1.le, hx.2⟩)
      simpa using this
  have hrect : ∀ R : ℝ, 0 ≤ R →
      ((∫ x in a..b, f ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)) -
          ∫ x in a..b, f ((x : ℂ) + (R : ℂ) * Complex.I)) +
        Complex.I • (∫ y in (-R)..R, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I • (∫ y in (-R)..R, f ((a : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    intro R _
    refine Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, -R⟩ ⟨b, R⟩ ?_
    refine hd.mono fun z hz => ?_
    exact (Set.uIcc_of_le hab).subset (Complex.mem_reProdIm.mp hz).1
  have hexp : Tendsto (fun R : ℝ => Real.exp (-R ^ 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero))
  have hH : Tendsto (fun R : ℝ => (∫ x in a..b, f ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)) -
      ∫ x in a..b, f ((x : ℂ) + (R : ℂ) * Complex.I)) atTop (𝓝 0) := by
    have hT : Tendsto (fun R : ℝ => 2 * (M * Real.exp (-R ^ 2) * (b - a))) atTop (𝓝 0) := by
      simpa using ((hexp.const_mul M).mul_const (b - a)).const_mul 2
    refine squeeze_zero_norm (fun R => ?_) hT
    calc _ ≤ ‖∫ x in a..b, f ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)‖ +
            ‖∫ x in a..b, f ((x : ℂ) + (R : ℂ) * Complex.I)‖ := norm_sub_le _ _
      _ ≤ M * Real.exp (-(-R) ^ 2) * (b - a) + M * Real.exp (-R ^ 2) * (b - a) :=
          add_le_add (hhor (-R)) (hhor R)
      _ = 2 * (M * Real.exp (-R ^ 2) * (b - a)) := by
          rw [neg_sq]
          ring
  have hVa : Tendsto (fun R : ℝ => ∫ y in (-R)..R, f ((a : ℂ) + (y : ℂ) * Complex.I)) atTop
      (𝓝 (∫ y : ℝ, f ((a : ℂ) + (y : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral (hint a ⟨le_rfl, hab⟩) tendsto_neg_atTop_atBot tendsto_id
  have hVb : Tendsto (fun R : ℝ => ∫ y in (-R)..R, f ((b : ℂ) + (y : ℂ) * Complex.I)) atTop
      (𝓝 (∫ y : ℝ, f ((b : ℂ) + (y : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral (hint b ⟨hab, le_rfl⟩) tendsto_neg_atTop_atBot tendsto_id
  have hlim := (hH.add (hVb.const_smul Complex.I)).sub (hVa.const_smul Complex.I)
  have heq : (0 : Y) + Complex.I • (∫ y : ℝ, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I • (∫ y : ℝ, f ((a : ℂ) + (y : ℂ) * Complex.I)) = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr'
      ((eventually_ge_atTop 0).mono fun R hR => (hrect R hR).symm))
  rw [zero_add, ← smul_sub, smul_eq_zero] at heq
  rcases heq with h | h
  · exact absurd h Complex.I_ne_zero
  · exact (sub_eq_zero.mp h).symm

/- English proof (translation)
Introduce `Y _ _ _ f a b M hab hd hb`. Conclude with `integral_vertical_line_eq f a b M hab hd hb`.
-/
theorem shift_vertical_line : ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (f : ℂ → Y) (a b M : ℝ), a ≤ b → DifferentiableOn ℂ f {z : ℂ | z.re ∈ Set.Icc a b} →
    (∀ z : ℂ, z.re ∈ Set.Icc a b → ‖f z‖ ≤ M * Real.exp (-z.im ^ 2)) →
    ∫ y : ℝ, f ⟨a, y⟩ = ∫ y : ℝ, f ⟨b, y⟩ := by
  intro Y _ _ _ f a b M hab hd hb
  exact integral_vertical_line_eq f a b M hab hd hb

end GlobalTheory.CompanionTheory.TubeFourier.ShiftLine
