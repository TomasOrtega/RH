import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

noncomputable section

open scoped ContDiff Topology
open Set MeasureTheory

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Introduce `V F _ _ _ _ _ _ p W Φ hW hWp hΦ`. Establish `h1 : (1 : WithTop ℕ∞) ≤ ∞` using `by exact_mod_cast le_top`. Establish `hdiff : DifferentiableOn ℝ Φ W` using `hΦ.differentiableOn (by simpa using h1)`. Use `set G : V × ℝ → V →L[ℝ] F := fun z => (fderiv ℝ Φ z).comp (ContinuousLinearMap.inl ℝ V ℝ) with hG`. Establish `hGc : ContinuousOn G W` using `(hΦ.continuousOn_fderiv_of_isOpen hW h1).clm_comp continuousOn_const`.

Establish `hpart : ∀ z ∈ W, HasFDerivAt (fun x => Φ (x, z.2)) (G z) z.1`. Introduce `z hz`. Establish `hz1 : HasFDerivAt Φ (fderiv ℝ Φ z) z` using `((hdiff z hz).differentiableAt (hW.mem_nhds hz)).hasFDerivAt`. Conclude with `hz1.comp z.1 (hasFDerivAt_prodMk_left z.1 z.2)`. Establish `hI : ∀ t ∈ Set.uIoc (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1`.

Introduce `t ht`. Rewrite `ht` using `[Set.uIoc_of_le zero_le_one]`. Conclude with `Ioc_subset_Icc_self ht`. Establish `hline : ∀ x : V, Continuous (fun t : ℝ => (x, t))` using `fun x => continuous_const.prodMk continuous_id`. Take `⟨u, v, hu, hv, hpu, hIv, huv⟩` from `generalized_tube_lemma isCompact_singleton isCompact_Icc hW (by`.

Introduce and unpack `⟨x, t⟩ ⟨hx, ht⟩`. Simplify using `only [mem_singleton_iff] at hx`. Substitute `hx` using the available equality. Conclude with `hWp t ht)`. Take `⟨ε, εpos, hball⟩` from `Metric.isOpen_iff.mp hu p (hpu rfl)`.

Establish `hε : 0 < ε / 2` using `half_pos εpos`. Establish `hKW : Metric.closedBall p (ε / 2) ×ˢ Icc (0 : ℝ) 1 ⊆ W`. Introduce and unpack `⟨x, t⟩ ⟨hx, ht⟩`. Conclude with `huv ⟨hball (Metric.closedBall_subset_ball (by linarith) hx), hIv ht⟩`. Establish `hKc : IsCompact (Metric.closedBall p (ε / 2) ×ˢ Icc (0 : ℝ) 1)` using `(isCompact_closedBall p (ε / 2)).prod isCompact_Icc`.

Take `⟨C, hC⟩` from `hKc.exists_bound_of_continuousOn (hGc.mono hKW)`. Establish `hpW : ∀ t ∈ Icc (0 : ℝ) 1, (p, t) ∈ W` using `hWp`. Establish `hcont1 : ContinuousOn (fun t : ℝ => G (p, t)) (Icc 0 1)` using `hGc.comp (hline p).continuousOn (fun t ht => hpW t ht)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `hcont1.congr ?_` and prove the remaining obligations.

Introduce `t ht`. Conclude with `(hpart (p, t) (hpW t ht)).fderiv`. Establish `hxW : ∀ x ∈ Metric.closedBall p (ε / 2), ∀ t ∈ Set.uIoc (0 : ℝ) 1, (x, t) ∈ W` using `fun x hx t ht => hKW ⟨hx, hI t ht⟩`. Establish `main` using `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (F := fun x t => Φ (x, t)) (F' := fun x t => G (x, t)) (bound := fun _ => C) (s := Metric.closedBall p (ε / 2)) (a := 0) (b := 1) (Metric.closedBall_mem_nhds p hε) (by filter_upwards [Metric.closedBall_ …`. Conclude with `(hΦ.continuousOn.comp (hline x).continuousOn (fun t ht => hxW x hx t ht)).aestronglyMeasurable measurableSet_uIoc)`.

Use the proof step `(by`. Apply `ContinuousOn.intervalIntegrable` to reduce the goal to its premises. Rewrite using `[Set.uIcc_of_le zero_le_one]`. Conclude with `hΦ.continuousOn.comp (hline p).continuousOn (fun t ht => hpW t ht))`. Use the proof step `((hcont1.mono (fun t ht => hI t ht)).aestronglyMeasurable measurableSet_uIoc)`.

Use the proof step `(Filter.Eventually.of_forall fun t ht x hx => hC _ ⟨hx, hI t ht⟩)`. Use `intervalIntegrable_const`. Use the proof step `(Filter.Eventually.of_forall fun t ht x hx => hpart (x, t) (hxW x hx t ht))`. Use `main.congr_fderiv ?_` and prove the remaining obligations. Apply `intervalIntegral.integral_congr` to reduce the goal to its premises.

Introduce `t ht`. Rewrite `ht` using `[Set.uIcc_of_le zero_le_one]`. Conclude with `((hpart (p, t) (hpW t ht)).fderiv).symm`.
-/
theorem paramDeriv : ParamDeriv := by
  intro V F _ _ _ _ _ _ p W Φ hW hWp hΦ
  have h1 : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hdiff : DifferentiableOn ℝ Φ W := hΦ.differentiableOn (by simpa using h1)
  set G : V × ℝ → V →L[ℝ] F := fun z => (fderiv ℝ Φ z).comp (ContinuousLinearMap.inl ℝ V ℝ) with hG
  have hGc : ContinuousOn G W :=
    (hΦ.continuousOn_fderiv_of_isOpen hW h1).clm_comp continuousOn_const
  have hpart : ∀ z ∈ W, HasFDerivAt (fun x => Φ (x, z.2)) (G z) z.1 := by
    intro z hz
    have hz1 : HasFDerivAt Φ (fderiv ℝ Φ z) z :=
      ((hdiff z hz).differentiableAt (hW.mem_nhds hz)).hasFDerivAt
    exact hz1.comp z.1 (hasFDerivAt_prodMk_left z.1 z.2)
  have hI : ∀ t ∈ Set.uIoc (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  have hline : ∀ x : V, Continuous (fun t : ℝ => (x, t)) := fun x =>
    continuous_const.prodMk continuous_id
  obtain ⟨u, v, hu, hv, hpu, hIv, huv⟩ := generalized_tube_lemma isCompact_singleton
    isCompact_Icc hW (by
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      simp only [mem_singleton_iff] at hx
      subst hx
      exact hWp t ht)
  obtain ⟨ε, εpos, hball⟩ := Metric.isOpen_iff.mp hu p (hpu rfl)
  have hε : 0 < ε / 2 := half_pos εpos
  have hKW : Metric.closedBall p (ε / 2) ×ˢ Icc (0 : ℝ) 1 ⊆ W := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact huv ⟨hball (Metric.closedBall_subset_ball (by linarith) hx), hIv ht⟩
  have hKc : IsCompact (Metric.closedBall p (ε / 2) ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall p (ε / 2)).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hGc.mono hKW)
  have hpW : ∀ t ∈ Icc (0 : ℝ) 1, (p, t) ∈ W := hWp
  have hcont1 : ContinuousOn (fun t : ℝ => G (p, t)) (Icc 0 1) :=
    hGc.comp (hline p).continuousOn (fun t ht => hpW t ht)
  refine ⟨?_, ?_⟩
  · refine hcont1.congr ?_
    intro t ht
    exact (hpart (p, t) (hpW t ht)).fderiv
  · have hxW : ∀ x ∈ Metric.closedBall p (ε / 2), ∀ t ∈ Set.uIoc (0 : ℝ) 1, (x, t) ∈ W :=
      fun x hx t ht => hKW ⟨hx, hI t ht⟩
    have main := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := volume) (F := fun x t => Φ (x, t)) (F' := fun x t => G (x, t))
      (bound := fun _ => C) (s := Metric.closedBall p (ε / 2)) (a := 0) (b := 1)
      (Metric.closedBall_mem_nhds p hε)
      (by
        filter_upwards [Metric.closedBall_mem_nhds p hε] with x hx
        exact (hΦ.continuousOn.comp (hline x).continuousOn
          (fun t ht => hxW x hx t ht)).aestronglyMeasurable measurableSet_uIoc)
      (by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le zero_le_one]
        exact hΦ.continuousOn.comp (hline p).continuousOn (fun t ht => hpW t ht))
      ((hcont1.mono (fun t ht => hI t ht)).aestronglyMeasurable measurableSet_uIoc)
      (Filter.Eventually.of_forall fun t ht x hx => hC _ ⟨hx, hI t ht⟩)
      intervalIntegrable_const
      (Filter.Eventually.of_forall fun t ht x hx => hpart (x, t) (hxW x hx t ht))
    refine main.congr_fderiv ?_
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact ((hpart (p, t) (hpW t ht)).fderiv).symm

end UpperTheory.V.Lit.Dr
