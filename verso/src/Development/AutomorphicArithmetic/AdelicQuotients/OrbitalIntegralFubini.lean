import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.NormEx
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotEq
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotFub
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open MeasureTheory Pointwise in
/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hP θ δ z hθ hz hinv hC hB φ hφ hφc`. Use `haveI : μ.IsHaarMeasure := hP.1.1`. Take `⟨ρ, hρc, hρn, hρD⟩` from `normEx G T μ j ν hP`. Establish `hw : Continuous fun x : G => x⁻¹ * δ * θ x` using `(continuous_inv.mul continuous_const).mul hθ`. Establish `hFm : Measurable (Function.uncurry fun (s : ℝ) (x : G) => φ (z s * (x⁻¹ * δ * θ x)))` using `(hφ.comp ((hz.comp continuous_fst).mul (hw.comp continuous_snd))).measurable`.

Establish `hwi : ∀ (t : T) (g : G), (j t * g)⁻¹ * δ * θ (j t * g) = g⁻¹ * δ * θ g`. Introduce `t g`. Establish `h` using `hinv t`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_inv_rev, map_mul, mul_assoc]`.

Use `_ = g⁻¹ * δ * θ g := by rw [h]`. Establish `hFi : ∀ (s : ℝ) (t : T) (g : G), φ (z s * ((j t * g)⁻¹ * δ * θ (j t * g))) = φ (z s * (g⁻¹ * δ * θ g))`. Introduce `s t g`. Rewrite using `[hwi]`. Take `⟨B, hBc, hBm⟩` from `hB (tsupport φ) hφc`.

Establish `hEc : IsCompact ((fun p : ℝ × G => (z p.1)⁻¹ * p.2) '' (B ×ˢ tsupport φ))` using `(hBc.prod hφc).image ((hz.comp continuous_fst).inv.mul continuous_snd)`. Take `⟨C, hCc, hCm⟩` from `hC _ hEc`. Take `⟨D, hDc, hDm⟩` from `hρD C hCc`. Establish `hsupp : ∀ (s : ℝ) (x : G), φ (z s * (x⁻¹ * δ * θ x)) ≠ 0 → s ∈ B ∧ x ∈ Set.range j * C`. Introduce `s x h`.

Establish `hm : z s * (x⁻¹ * δ * θ x) ∈ tsupport φ` using `subset_tsupport φ (Function.mem_support.2 h)`. Establish `hs` using `hBm s x hm`. Establish `he : x⁻¹ * δ * θ x ∈ (fun p : ℝ × G => (z p.1)⁻¹ * p.2) '' (B ×ˢ tsupport φ)` using `⟨(s, z s * (x⁻¹ * δ * θ x)), ⟨hs, hm⟩, by simp⟩`. Take `⟨t, y, hy, hx⟩` from `hCm x he`. Conclude with `⟨hs, Set.mem_mul.2 ⟨j t, ⟨t, rfl⟩, y, hy, hx.symm⟩⟩`.

Take `⟨M, hM⟩` from `hφc.exists_bound_of_continuous hφ`. Take `⟨R, hR⟩` from `hDc.exists_bound_of_continuousOn (f := fun x => ((ρ x : NNReal) : ℝ)) (NNReal.continuous_coe.comp hρc).continuousOn`. Establish `hpt : ∀ (s : ℝ) (x : G), ‖φ (z s * (x⁻¹ * δ * θ x))‖ₑ * (ρ x : ENNReal) ≤ D.indicator (fun _ => ENNReal.ofReal M * ENNReal.ofReal R) x`. Introduce `s x`. Distinguish the cases in `h0 : φ (z s * (x⁻¹ * δ * θ x)) = 0`.

Simplify using `[h0]`. Distinguish the cases in `h1 : ρ x = 0`. Simplify using `[h1]`. Establish `hx : x ∈ D` using `hDm x (hsupp s x h0).2 h1`. Rewrite using `[Set.indicator_of_mem hx]`.

Use `mul_le_mul' ?_ ?_` and prove the remaining obligations. Rewrite using `[← ofReal_norm_eq_enorm]`. Conclude with `ENNReal.ofReal_le_ofReal (hM _)`. Rewrite using `[← ENNReal.ofReal_coe_nnreal]`. Conclude with `ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hR x hx))`.

Establish `hin : ∀ s : ℝ, ∫⁻ x, ‖φ (z s * (x⁻¹ * δ * θ x))‖ₑ * (ρ x : ENNReal) ∂μ ≤ B.indicator (fun _ => ENNReal.ofReal M * ENNReal.ofReal R * μ D) s`. Introduce `s`. Distinguish the cases in `hs : s ∈ B`. Rewrite using `[Set.indicator_of_mem hs, ← lintegral_indicator_const hDc.measurableSet]`. Conclude with `lintegral_mono fun x => hpt s x`.

Establish `h0 : ∀ x : G, φ (z s * (x⁻¹ * δ * θ x)) = 0` using `fun x => by`. Assume the negation of the conclusion as `h`. Conclude with `hs (hsupp s x h).1`. Simplify using `[h0]`. Establish `hfin : ∫⁻ s : ℝ, ∫⁻ x, ‖φ (z s * (x⁻¹ * δ * θ x))‖ₑ * (ρ x : ENNReal) ∂μ ≠ ⊤`.

Use `ne_top_of_le_ne_top ?_ (lintegral_mono hin)` and prove the remaining obligations. Rewrite using `[lintegral_indicator_const hBc.measurableSet]`. Conclude with `ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hDc.measure_lt_top.ne) hBc.measure_lt_top.ne`. Take `⟨h1, h2⟩` from `quotFub_of normEx quotEq G T μ j ν hP ℝ volume (fun s x => φ (z s * (x⁻¹ * δ * θ x))) hFm hFi (fun x => (ρ x : ENNReal)) hρn hfin`. Conclude with `⟨h1.1, h2⟩`.
-/
theorem UpperTheory.orbital_integral_fubini :
    Fub := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hP θ δ z hθ hz hinv hC hB φ hφ hφc
  haveI : μ.IsHaarMeasure := hP.1.1
  obtain ⟨ρ, hρc, hρn, hρD⟩ := normEx G T μ j ν hP
  have hw : Continuous fun x : G => x⁻¹ * δ * θ x :=
    (continuous_inv.mul continuous_const).mul hθ
  have hFm : Measurable (Function.uncurry fun (s : ℝ) (x : G) => φ (z s * (x⁻¹ * δ * θ x))) :=
    (hφ.comp ((hz.comp continuous_fst).mul (hw.comp continuous_snd))).measurable
  have hwi : ∀ (t : T) (g : G), (j t * g)⁻¹ * δ * θ (j t * g) = g⁻¹ * δ * θ g := by
    intro t g
    have h := hinv t
    calc (j t * g)⁻¹ * δ * θ (j t * g) = g⁻¹ * ((j t)⁻¹ * δ * θ (j t)) * θ g := by
          simp only [mul_inv_rev, map_mul, mul_assoc]
      _ = g⁻¹ * δ * θ g := by rw [h]
  have hFi : ∀ (s : ℝ) (t : T) (g : G),
      φ (z s * ((j t * g)⁻¹ * δ * θ (j t * g))) = φ (z s * (g⁻¹ * δ * θ g)) := by
    intro s t g
    rw [hwi]
  obtain ⟨B, hBc, hBm⟩ := hB (tsupport φ) hφc
  have hEc : IsCompact ((fun p : ℝ × G => (z p.1)⁻¹ * p.2) '' (B ×ˢ tsupport φ)) :=
    (hBc.prod hφc).image ((hz.comp continuous_fst).inv.mul continuous_snd)
  obtain ⟨C, hCc, hCm⟩ := hC _ hEc
  obtain ⟨D, hDc, hDm⟩ := hρD C hCc
  have hsupp : ∀ (s : ℝ) (x : G), φ (z s * (x⁻¹ * δ * θ x)) ≠ 0 →
      s ∈ B ∧ x ∈ Set.range j * C := by
    intro s x h
    have hm : z s * (x⁻¹ * δ * θ x) ∈ tsupport φ := subset_tsupport φ (Function.mem_support.2 h)
    have hs := hBm s x hm
    have he : x⁻¹ * δ * θ x ∈ (fun p : ℝ × G => (z p.1)⁻¹ * p.2) '' (B ×ˢ tsupport φ) :=
      ⟨(s, z s * (x⁻¹ * δ * θ x)), ⟨hs, hm⟩, by simp⟩
    obtain ⟨t, y, hy, hx⟩ := hCm x he
    exact ⟨hs, Set.mem_mul.2 ⟨j t, ⟨t, rfl⟩, y, hy, hx.symm⟩⟩
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  obtain ⟨R, hR⟩ := hDc.exists_bound_of_continuousOn (f := fun x => ((ρ x : NNReal) : ℝ))
    (NNReal.continuous_coe.comp hρc).continuousOn
  have hpt : ∀ (s : ℝ) (x : G), ‖φ (z s * (x⁻¹ * δ * θ x))‖ₑ * (ρ x : ENNReal) ≤
      D.indicator (fun _ => ENNReal.ofReal M * ENNReal.ofReal R) x := by
    intro s x
    by_cases h0 : φ (z s * (x⁻¹ * δ * θ x)) = 0
    · simp [h0]
    by_cases h1 : ρ x = 0
    · simp [h1]
    have hx : x ∈ D := hDm x (hsupp s x h0).2 h1
    rw [Set.indicator_of_mem hx]
    refine mul_le_mul' ?_ ?_
    · rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM _)
    · rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hR x hx))
  have hin : ∀ s : ℝ, ∫⁻ x, ‖φ (z s * (x⁻¹ * δ * θ x))‖ₑ * (ρ x : ENNReal) ∂μ ≤
      B.indicator (fun _ => ENNReal.ofReal M * ENNReal.ofReal R * μ D) s := by
    intro s
    by_cases hs : s ∈ B
    · rw [Set.indicator_of_mem hs, ← lintegral_indicator_const hDc.measurableSet]
      exact lintegral_mono fun x => hpt s x
    · have h0 : ∀ x : G, φ (z s * (x⁻¹ * δ * θ x)) = 0 := fun x => by
        by_contra h
        exact hs (hsupp s x h).1
      simp [h0]
  have hfin : ∫⁻ s : ℝ, ∫⁻ x, ‖φ (z s * (x⁻¹ * δ * θ x))‖ₑ * (ρ x : ENNReal) ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hin)
    rw [lintegral_indicator_const hBc.measurableSet]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hDc.measure_lt_top.ne)
      hBc.measure_lt_top.ne
  obtain ⟨h1, h2⟩ := quotFub_of normEx quotEq G T μ j ν hP ℝ volume
    (fun s x => φ (z s * (x⁻¹ * δ * θ x))) hFm hFi (fun x => (ρ x : ENNReal)) hρn hfin
  exact ⟨h1.1, h2⟩
