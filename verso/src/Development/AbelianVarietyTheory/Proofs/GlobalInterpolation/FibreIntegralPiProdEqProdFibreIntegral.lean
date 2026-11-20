import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Set Topology
open scoped ENNReal

namespace GlobalTheory.FibreProd

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Take `⟨c, hc1, hc2⟩` from `exists_between hlt`. Take `⟨d, hd1, hd2⟩` from `exists_between hc2`. Establish `e : ∀ᶠ x in 𝓝 b, G x < c ∧ d < H x` using `(hG.eventually (gt_mem_nhds hc1)).and (hH.eventually (lt_mem_nhds hd2))`.

Take `⟨r, hr, hb⟩` from `Metric.eventually_nhds_iff_ball.1 e`. Establish `h1 : ∫⁻ x in Metric.ball b r, G x ∂ν ≤ c * ν (Metric.ball b r)`. Rewrite using `[← setLIntegral_const]`. Conclude with `setLIntegral_mono' measurableSet_ball fun x hx => (hb x hx).1.le`. Establish `h2 : d * ν (Metric.ball b r) ≤ ∫⁻ x in Metric.ball b r, H x ∂ν`.

Rewrite using `[← setLIntegral_const]`. Conclude with `setLIntegral_mono' measurableSet_ball fun x hx => (hb x hx).2.le`. Establish `h3 : c * ν (Metric.ball b r) < d * ν (Metric.ball b r)` using `ENNReal.mul_lt_mul_left (Metric.measure_ball_pos ν b hr).ne' measure_ball_lt_top.ne hd1`. Conclude with `absurd (h2.trans ((h r hr).symm.le.trans h1)) h3.not_ge`.
-/
theorem le_of_lintegral_ball_eq {X : Type} [PseudoMetricSpace X] [ProperSpace X] [MeasurableSpace X]
    [BorelSpace X] (ν : Measure X) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    (G H : X → ℝ≥0∞) (b : X) (hG : ContinuousAt G b) (hH : ContinuousAt H b)
    (h : ∀ r > 0, ∫⁻ x in Metric.ball b r, G x ∂ν = ∫⁻ x in Metric.ball b r, H x ∂ν) :
    H b ≤ G b := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  obtain ⟨d, hd1, hd2⟩ := exists_between hc2
  have e : ∀ᶠ x in 𝓝 b, G x < c ∧ d < H x :=
    (hG.eventually (gt_mem_nhds hc1)).and (hH.eventually (lt_mem_nhds hd2))
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 e
  have h1 : ∫⁻ x in Metric.ball b r, G x ∂ν ≤ c * ν (Metric.ball b r) := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hb x hx).1.le
  have h2 : d * ν (Metric.ball b r) ≤ ∫⁻ x in Metric.ball b r, H x ∂ν := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hb x hx).2.le
  have h3 : c * ν (Metric.ball b r) < d * ν (Metric.ball b r) :=
    ENNReal.mul_lt_mul_left (Metric.measure_ball_pos ν b hr).ne' measure_ball_lt_top.ne hd1
  exact absurd (h2.trans ((h r hr).symm.le.trans h1)) h3.not_ge

/- English proof (translation)
Establish `h2` using `h.2.1 ((f ⁻¹' S).indicator φ) (hφ.indicator (hf hS))`. Establish `e1 : ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ v in U, (f ⁻¹' S).indicator φ v ∂μ`. Rewrite using `[← lintegral_indicator hU.measurableSet]`. Use `congr 1`. Use function extensionality and compare the values at `v`.

Distinguish the cases in `hv : v ∈ U`. Rewrite using `[indicator_of_mem hv]`. Rewrite using `[indicator_of_notMem hv]`. Conclude with `indicator_apply_eq_zero.2 fun _ => hs v hv`. Rewrite using `[e1, h2, ← lintegral_indicator hS]`.

Use `congr 1`. Use function extensionality and compare the values at `b`. Establish `hb : ∀ᵐ v ∂(fib b), f v = b`. Establish `: ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {id b} ∩ U` using `h.1 b`. Use `filter_upwards [this] with v hv using hv.1`.

Distinguish the cases in `hbS : b ∈ S`. Rewrite using `[indicator_of_mem hbS]`. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hb] with v hv`. Conclude with `indicator_of_mem (by simpa [hv] using hbS) _`.

Rewrite using `[indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]`. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hb] with v hv`. Conclude with `indicator_of_notMem (by simpa [hv] using hbS) _`.
-/
theorem lintegral_preimage {V X : Type} [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X}
    {f : V → X} {U : Set V} {B : Set X} {fib : X → Measure V}
    (hf : Measurable f) (hU : IsOpen U) (h : IsFibreFamily μ f id U ν B fib)
    (φ : V → ℝ≥0∞) (hφ : Measurable φ) (hs : ∀ v, v ∉ U → φ v = 0)
    (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) ∂ν := by
  have h2 := h.2.1 ((f ⁻¹' S).indicator φ) (hφ.indicator (hf hS))
  have e1 : ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ v in U, (f ⁻¹' S).indicator φ v ∂μ := by
    rw [← lintegral_indicator hU.measurableSet]
    congr 1
    funext v
    by_cases hv : v ∈ U
    · rw [indicator_of_mem hv]
    · rw [indicator_of_notMem hv]
      exact indicator_apply_eq_zero.2 fun _ => hs v hv
  rw [e1, h2, ← lintegral_indicator hS]
  congr 1
  funext b
  have hb : ∀ᵐ v ∂(fib b), f v = b := by
    have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {id b} ∩ U := h.1 b
    filter_upwards [this] with v hv using hv.1
  by_cases hbS : b ∈ S
  · rw [indicator_of_mem hbS]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_mem (by simpa [hv] using hbS) _
  · rw [indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_notMem (by simpa [hv] using hbS) _

/- English proof (translation)
Introduce `T V _ _ _ _ _ _ μ₀ _ q hq U hU fib hfib B hB Fib hFib b hb φ hφ`. Use `haveI : ProperSpace V := FiniteDimensional.proper_real V`. Establish `hΦc : Continuous fun x : T → V => ∏ ρ, φ ρ (x ρ)` using `continuous_finset_prod _ fun ρ _ => (hφ ρ).1.comp (continuous_apply ρ)`. Establish `hΦs : HasCompactSupport fun x : T → V => ∏ ρ, φ ρ (x ρ)`. Use `HasCompactSupport.intro (isCompact_univ_pi fun ρ => (hφ ρ).2.1) fun x hx => ?_` and prove the remaining obligations.

Rewrite `hx` using `[mem_univ_pi, not_forall]`. Take `⟨ρ, hρ⟩` from `hx`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ ρ) (image_eq_zero_of_notMem_tsupport hρ)`. Take `⟨hI, hC⟩` from `hFib.2.2 _ hΦc hΦs (subset_univ _)`. Establish `hm : ∀ ρ, Measurable fun y => ENNReal.ofReal (φ ρ y)` using `fun ρ => ENNReal.measurable_ofReal.comp (hφ ρ).1.measurable`.

Establish `hGc : ContinuousOn (fun b => ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b)) B`. Use `(ENNReal.continuous_ofReal.comp_continuousOn hC).congr fun b hb => ?_` and prove the remaining obligations. Use `ofReal_integral_eq_lintegral_ofReal (hI b hb) (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun ρ _ => (hφ ρ).2.2.2 _)` as an intermediate fact. Simplify using `only [Function.comp_apply]`. Rewrite using `[this]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[ENNReal.ofReal_prod_of_nonneg fun ρ _ => (hφ ρ).2.2.2 _]`. Establish `hg : ∀ ρ t, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t) = ENNReal.ofReal (∫ y, φ ρ y ∂(fib t))` using `fun ρ t => (ofReal_integral_eq_lintegral_ofReal ((hfib.2.2 _ (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).1 t (mem_univ _)) (Filter.Eventually.of_forall (hφ ρ).2.2.2)).symm`. Establish `hgc : ∀ ρ, Continuous fun t => ∫ y, φ ρ y ∂(fib t)` using `fun ρ => continuousOn_univ.1 (hfib.2.2 _ (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).2`.

Establish `hgm : ∀ ρ, Measurable fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t)` using `fun ρ => by`. Simplify using `only [hg]`. Conclude with `ENNReal.measurable_ofReal.comp (hgc ρ).measurable`. Establish `hHc : Continuous fun b : T → ℝ => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ))`. Establish `: (fun b : T → ℝ => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ))) = fun b => ENNReal.ofReal (∏ ρ, ∫ y, φ ρ y ∂(fib (b ρ)))`.

Use function extensionality and compare the values at `b`. Rewrite using `[ENNReal.ofReal_prod_of_nonneg fun ρ _ => integral_nonneg (hφ ρ).2.2.2]`. Simplify using `only [hg]`. Rewrite using `[this]`. Conclude with `ENNReal.continuous_ofReal.comp (continuous_finset_prod _ fun ρ _ => (hgc ρ).comp (continuous_apply ρ))`.

Establish `key : ∀ r > 0, ∫⁻ c in Metric.ball b r, ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib c) = ∫⁻ c in Metric.ball b r, ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (c ρ))`. Introduce `r hr`. Establish `hQ : Measurable fun (x : T → V) ρ => q (x ρ)` using `(continuous_pi fun ρ => hq.comp (continuous_apply ρ)).measurable`. Rewrite using `[← lintegral_preimage hQ isOpen_univ hFib (fun x => ∏ ρ, ENNReal.ofReal (φ ρ (x ρ))) (Finset.measurable_prod _ fun ρ _ => (hm ρ).comp (measurable_pi_apply ρ)) (fun v hv => absurd (mem_univ v) hv) _ measurableSet_ball, ← lintegral_indicator measurableSet_ball, ball_pi b hr]`. Establish `e1 : ∀ x : T → V, ((fun (x : T → V) ρ => q (x ρ)) ⁻¹' (Set.pi univ fun ρ => Metric.ball (b ρ) r)).indicator (fun x => ∏ ρ, ENNReal.ofReal (φ ρ (x ρ))) x = ∏ ρ, (q ⁻¹' Metric.ball (b ρ) r).indicator (fun y => ENNReal.ofReal (φ ρ y)) (x ρ)`.

Introduce `x`. Distinguish the cases in `hx : ∀ ρ, x ρ ∈ q ⁻¹' Metric.ball (b ρ) r`. Rewrite using `[indicator_of_mem (by simpa using hx)]`. Conclude with `Finset.prod_congr rfl fun ρ _ => by rw [indicator_of_mem (hx ρ)]`. Rewrite using `[indicator_of_notMem (by simpa using hx)]`.

Take `⟨ρ, hρ⟩` from `not_forall.1 hx`. Conclude with `(Finset.prod_eq_zero (Finset.mem_univ ρ) (indicator_of_notMem hρ _)).symm`. Establish `e2 : ∀ c : T → ℝ, (Set.pi univ fun ρ => Metric.ball (b ρ) r).indicator (fun c => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (c ρ))) c = ∏ ρ, (Metric.ball (b ρ) r).indicator (fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t)) (c ρ)`. Introduce `c`. Distinguish the cases in `hx : ∀ ρ, c ρ ∈ Metric.ball (b ρ) r`.

Rewrite using `[indicator_of_mem (by simpa using hx)]`. Conclude with `Finset.prod_congr rfl fun ρ _ => by rw [indicator_of_mem (hx ρ)]`. Rewrite using `[indicator_of_notMem (by simpa using hx)]`. Take `⟨ρ, hρ⟩` from `not_forall.1 hx`. Conclude with `(Finset.prod_eq_zero (Finset.mem_univ ρ) (indicator_of_notMem hρ _)).symm`.

Simplify using `only [e1, e2]`. Rewrite using `[volume_pi, GlobalTheory.SnMass.Push.lintegral_fintype_prod (fun ρ => (q ⁻¹' Metric.ball (b ρ) r).indicator (fun y => ENNReal.ofReal (φ ρ y))) (fun ρ => (hm ρ).indicator (hq.measurable measurableSet_ball)), GlobalTheory.SnMass.Push.lintegral_fintype_prod (fun ρ => (Metric.ball (b …`. Use `Finset.prod_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[lintegral_indicator (s := Metric.ball (b ρ) r) measurableSet_ball]`. Use `lintegral_preimage hq.measurable hU hfib _ (hm ρ) (fun v hv => ?_) _ measurableSet_ball` and prove the remaining obligations.

Rewrite using `[image_eq_zero_of_notMem_tsupport fun h => hv ((hφ ρ).2.2.1 h), ENNReal.ofReal_zero]`. Establish `hGb` using `hGc.continuousAt (hB.mem_nhds hb)`. Conclude with `le_antisymm (le_of_lintegral_ball_eq volume _ _ b hHc.continuousAt hGb fun r hr => (key r hr).symm) (le_of_lintegral_ball_eq volume _ _ b hGb hHc.continuousAt key)`.
-/
theorem lintegral_fibre_prod : ∀ (T V : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ₀ : Measure V) [SigmaFinite μ₀] (q : V → ℝ), Continuous q → ∀ U : Set V, IsOpen U → ∀ fib : ℝ → Measure V, IsFibreFamily μ₀ q id U (volume : Measure ℝ) Set.univ fib → ∀ B : Set (T → ℝ), IsOpen B → ∀ Fib : (T → ℝ) → Measure (T → V), IsFibreFamily (Measure.pi fun _ : T => μ₀) (fun x ρ => q (x ρ)) id Set.univ (volume : Measure (T → ℝ)) B Fib → ∀ b ∈ B, ∀ φ : T → V → ℝ, (∀ ρ, Continuous (φ ρ) ∧ HasCompactSupport (φ ρ) ∧ tsupport (φ ρ) ⊆ U ∧ ∀ y, 0 ≤ φ ρ y) → ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b) = ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
  intro T V _ _ _ _ _ _ μ₀ _ q hq U hU fib hfib B hB Fib hFib b hb φ hφ
  classical
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  have hΦc : Continuous fun x : T → V => ∏ ρ, φ ρ (x ρ) :=
    continuous_finset_prod _ fun ρ _ => (hφ ρ).1.comp (continuous_apply ρ)
  have hΦs : HasCompactSupport fun x : T → V => ∏ ρ, φ ρ (x ρ) := by
    refine HasCompactSupport.intro (isCompact_univ_pi fun ρ => (hφ ρ).2.1) fun x hx => ?_
    rw [mem_univ_pi, not_forall] at hx
    obtain ⟨ρ, hρ⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ ρ) (image_eq_zero_of_notMem_tsupport hρ)
  obtain ⟨hI, hC⟩ := hFib.2.2 _ hΦc hΦs (subset_univ _)
  have hm : ∀ ρ, Measurable fun y => ENNReal.ofReal (φ ρ y) := fun ρ =>
    ENNReal.measurable_ofReal.comp (hφ ρ).1.measurable
  have hGc : ContinuousOn (fun b => ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b)) B := by
    refine (ENNReal.continuous_ofReal.comp_continuousOn hC).congr fun b hb => ?_
    have := ofReal_integral_eq_lintegral_ofReal (hI b hb)
      (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun ρ _ => (hφ ρ).2.2.2 _)
    simp only [Function.comp_apply]
    rw [this]
    congr 1
    funext x
    rw [ENNReal.ofReal_prod_of_nonneg fun ρ _ => (hφ ρ).2.2.2 _]
  have hg : ∀ ρ t, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t) = ENNReal.ofReal (∫ y, φ ρ y ∂(fib t)) :=
    fun ρ t => (ofReal_integral_eq_lintegral_ofReal
      ((hfib.2.2 _ (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).1 t (mem_univ _))
      (Filter.Eventually.of_forall (hφ ρ).2.2.2)).symm
  have hgc : ∀ ρ, Continuous fun t => ∫ y, φ ρ y ∂(fib t) := fun ρ =>
    continuousOn_univ.1 (hfib.2.2 _ (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).2
  have hgm : ∀ ρ, Measurable fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t) := fun ρ => by
    simp only [hg]
    exact ENNReal.measurable_ofReal.comp (hgc ρ).measurable
  have hHc : Continuous fun b : T → ℝ => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
    have : (fun b : T → ℝ => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ))) =
        fun b => ENNReal.ofReal (∏ ρ, ∫ y, φ ρ y ∂(fib (b ρ))) := by
      funext b
      rw [ENNReal.ofReal_prod_of_nonneg fun ρ _ => integral_nonneg (hφ ρ).2.2.2]
      simp only [hg]
    rw [this]
    exact ENNReal.continuous_ofReal.comp
      (continuous_finset_prod _ fun ρ _ => (hgc ρ).comp (continuous_apply ρ))
  have key : ∀ r > 0, ∫⁻ c in Metric.ball b r, ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib c) =
      ∫⁻ c in Metric.ball b r, ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (c ρ)) := by
    intro r hr
    have hQ : Measurable fun (x : T → V) ρ => q (x ρ) :=
      (continuous_pi fun ρ => hq.comp (continuous_apply ρ)).measurable
    rw [← lintegral_preimage hQ isOpen_univ hFib (fun x => ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)))
      (Finset.measurable_prod _ fun ρ _ => (hm ρ).comp (measurable_pi_apply ρ))
      (fun v hv => absurd (mem_univ v) hv) _ measurableSet_ball,
      ← lintegral_indicator measurableSet_ball, ball_pi b hr]
    have e1 : ∀ x : T → V, ((fun (x : T → V) ρ => q (x ρ)) ⁻¹'
        (Set.pi univ fun ρ => Metric.ball (b ρ) r)).indicator
        (fun x => ∏ ρ, ENNReal.ofReal (φ ρ (x ρ))) x =
        ∏ ρ, (q ⁻¹' Metric.ball (b ρ) r).indicator (fun y => ENNReal.ofReal (φ ρ y)) (x ρ) := by
      intro x
      by_cases hx : ∀ ρ, x ρ ∈ q ⁻¹' Metric.ball (b ρ) r
      · rw [indicator_of_mem (by simpa using hx)]
        exact Finset.prod_congr rfl fun ρ _ => by rw [indicator_of_mem (hx ρ)]
      · rw [indicator_of_notMem (by simpa using hx)]
        obtain ⟨ρ, hρ⟩ := not_forall.1 hx
        exact (Finset.prod_eq_zero (Finset.mem_univ ρ) (indicator_of_notMem hρ _)).symm
    have e2 : ∀ c : T → ℝ, (Set.pi univ fun ρ => Metric.ball (b ρ) r).indicator
        (fun c => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (c ρ))) c =
        ∏ ρ, (Metric.ball (b ρ) r).indicator
          (fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t)) (c ρ) := by
      intro c
      by_cases hx : ∀ ρ, c ρ ∈ Metric.ball (b ρ) r
      · rw [indicator_of_mem (by simpa using hx)]
        exact Finset.prod_congr rfl fun ρ _ => by rw [indicator_of_mem (hx ρ)]
      · rw [indicator_of_notMem (by simpa using hx)]
        obtain ⟨ρ, hρ⟩ := not_forall.1 hx
        exact (Finset.prod_eq_zero (Finset.mem_univ ρ) (indicator_of_notMem hρ _)).symm
    simp only [e1, e2]
    rw [volume_pi, GlobalTheory.SnMass.Push.lintegral_fintype_prod
        (fun ρ => (q ⁻¹' Metric.ball (b ρ) r).indicator (fun y => ENNReal.ofReal (φ ρ y)))
        (fun ρ => (hm ρ).indicator (hq.measurable measurableSet_ball)),
      GlobalTheory.SnMass.Push.lintegral_fintype_prod
        (fun ρ => (Metric.ball (b ρ) r).indicator
          (fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t)))
        (fun ρ => (hgm ρ).indicator measurableSet_ball)]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [lintegral_indicator (s := Metric.ball (b ρ) r) measurableSet_ball]
    refine lintegral_preimage hq.measurable hU hfib _ (hm ρ) (fun v hv => ?_) _ measurableSet_ball
    rw [image_eq_zero_of_notMem_tsupport fun h => hv ((hφ ρ).2.2.1 h), ENNReal.ofReal_zero]
  have hGb := hGc.continuousAt (hB.mem_nhds hb)
  exact le_antisymm
    (le_of_lintegral_ball_eq volume _ _ b hHc.continuousAt hGb fun r hr => (key r hr).symm)
    (le_of_lintegral_ball_eq volume _ _ b hGb hHc.continuousAt key)

end GlobalTheory.FibreProd
