import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtWeak
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegBall

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

/- English proof (translation)
Introduce `n Ω F u hΩ hF hu hint`. Take `⟨U, hU, hae⟩` from `reg n Ω _ hΩ (extWeak n Ω F u hΩ hF hu hint)`. Use `⟨U, hU, ?_⟩` and prove the remaining obligations. Establish `hW : IsOpen (Ω \ {z | F z = 0})`. Rewrite using `[Set.diff_eq]`.

Conclude with `hF.continuousOn.isOpen_inter_preimage hΩ isOpen_compl_singleton`. Establish `hae' : (Ω \ {z | F z = 0}).indicator u =ᵐ[volume.restrict (Ω \ {z | F z = 0})] U` using `ae_restrict_of_ae_restrict_of_subset diff_subset hae`. Establish `hae'' : u =ᵐ[volume.restrict (Ω \ {z | F z = 0})] U` using `by filter_upwards [hae', ae_restrict_mem hW.measurableSet] with z hz hzW`. Rewrite using `[← hz, Set.indicator_of_mem hzW]`. Conclude with `(Measure.eqOn_open_of_ae_eq hae'' hW hu.continuousOn (hU.continuousOn.mono diff_subset)).symm`.
-/
theorem ext : ExtStatement := by
  intro n Ω F u hΩ hF hu hint
  obtain ⟨U, hU, hae⟩ := reg n Ω _ hΩ (extWeak n Ω F u hΩ hF hu hint)
  refine ⟨U, hU, ?_⟩
  have hW : IsOpen (Ω \ {z | F z = 0}) := by
    rw [Set.diff_eq]
    exact hF.continuousOn.isOpen_inter_preimage hΩ isOpen_compl_singleton
  have hae' : (Ω \ {z | F z = 0}).indicator u =ᵐ[volume.restrict (Ω \ {z | F z = 0})] U :=
    ae_restrict_of_ae_restrict_of_subset diff_subset hae
  have hae'' : u =ᵐ[volume.restrict (Ω \ {z | F z = 0})] U := by
    filter_upwards [hae', ae_restrict_mem hW.measurableSet] with z hz hzW
    rw [← hz, Set.indicator_of_mem hzW]
  exact (Measure.eqOn_open_of_ae_eq hae'' hW hu.continuousOn
    (hU.continuousOn.mono diff_subset)).symm

/- English proof (translation)
Introduce and unpack `n c R F hF ⟨z0, hz0, hFz0⟩`. Use `set Ω := ball c R with hΩdef`. Use `set Z := {z | F z = 0} with hZdef`. Establish `hΩ : IsOpen Ω` using `isOpen_ball`. Establish `hW : IsOpen (Ω \ Z)`.

Rewrite using `[Set.diff_eq]`. Conclude with `hF.continuousOn.isOpen_inter_preimage hΩ isOpen_compl_singleton`. Establish `hmeas : MeasurableSet (Ω ∩ Z)`. Rewrite using `[← Set.diff_diff_right_self]`. Conclude with `hΩ.measurableSet.diff hW.measurableSet`.

Establish `hint : IntegrableOn (fun z => ‖(fun _ => (1 : ℂ)) z‖ ^ 2) (Ω \ Z)`. Simplify using `only [norm_one, one_pow]`. Conclude with `integrableOn_const ((measure_mono diff_subset).trans_lt measure_ball_lt_top).ne`. Establish `hwk` using `extWeak n Ω F (fun _ => 1) hΩ hF (differentiableOn_const 1) hint`. Take `⟨U, hU, hae⟩` from `reg n Ω _ hΩ hwk`.

Establish `hae1 : (fun _ => (1 : ℂ)) =ᵐ[volume.restrict (Ω \ Z)] U` using `by filter_upwards [ae_restrict_of_ae_restrict_of_subset diff_subset hae, ae_restrict_mem hW.measurableSet] with z hz hzW`. Rewrite using `[← hz, Set.indicator_of_mem hzW]`. Establish `hEq1 : EqOn (fun _ => (1 : ℂ)) U (Ω \ Z)` using `Measure.eqOn_open_of_ae_eq hae1 hW continuousOn_const (hU.continuousOn.mono diff_subset)`. Establish `hz0W : z0 ∈ Ω \ Z` using `⟨hz0, hFz0⟩`. Establish `hUall : EqOn U (fun _ => (1 : ℂ)) Ω`.

Introduce `z hz`. Use `set L : ℂ → V n := fun t => z0 + t • (z - z0) with hLdef`. Use `set S : Set ℂ := L ⁻¹' Ω with hSdef`. Establish `hLd : Differentiable ℂ L` using `(differentiable_const _).add (differentiable_id.smul_const _)`. Establish `hLc : Continuous L` using `hLd.continuous`.

Establish `hSo : IsOpen S` using `hΩ.preimage hLc`. Establish `hSconv : Convex ℝ S`. Introduce `t1 ht1 t2 ht2 a b ha hb hab`. Establish `hm` using `(convex_ball c R) ht1 ht2 ha hb hab`. Use `show z0 + (a • t1 + b • t2) • (z - z0) ∈ Ω`.

Establish `e : z0 + (a • t1 + b • t2) • (z - z0) = a • (z0 + t1 • (z - z0)) + b • (z0 + t2 • (z - z0))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hab, one_smul, add_smul, smul_assoc, smul_assoc]`. Use `_ = a • (z0 + t1 • (z - z0)) + b • (z0 + t2 • (z - z0)) := by`. Rewrite using `[add_smul, smul_add, smul_add]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `hm`. Establish `hga : AnalyticOnNhd ℂ (U ∘ L) S` using `(hU.comp hLd.differentiableOn fun t ht => ht).analyticOnNhd hSo`. Establish `h0S : (0 : ℂ) ∈ S` using `by show z0 + (0 : ℂ) • (z - z0) ∈ Ω`.

Simplify using `using hz0`. Establish `h1S : (1 : ℂ) ∈ S` using `by show z0 + (1 : ℂ) • (z - z0) ∈ Ω`. Simplify using `using hz`. Establish `hL0 : L 0 = z0` using `by simp [hLdef]`. Establish `hev : (U ∘ L) =ᶠ[𝓝 0] fun _ => (1 : ℂ)`.

Establish `hpre : L ⁻¹' (Ω \ Z) ∈ 𝓝 (0 : ℂ)` using `hLc.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hW.mem_nhds hz0W)`. Use `filter_upwards [hpre] with t ht using (hEq1 ht).symm`. Establish `h1` using `hga.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hSconv.isPreconnected h0S hev h1S`. Simplify `h1` using `[hLdef]`. Establish `hZ : ∀ᵐ z ∂volume.restrict (Ω ∩ Z), False` using `by filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hae, ae_restrict_mem hmeas] with z hz hzZ`.

Rewrite `hz` using `[Set.indicator_of_notMem (fun h => h.2 hzZ.2), hUall hzZ.1]`. Conclude with `zero_ne_one hz`. Establish `h0 : volume.restrict (Ω ∩ Z) = 0` using `ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hZ)`. Conclude with `Measure.restrict_eq_zero.1 h0`.
-/
theorem extNull : ExtNullStatement := by
  rintro n c R F hF ⟨z0, hz0, hFz0⟩
  set Ω := ball c R with hΩdef
  set Z := {z | F z = 0} with hZdef
  have hΩ : IsOpen Ω := isOpen_ball
  have hW : IsOpen (Ω \ Z) := by
    rw [Set.diff_eq]
    exact hF.continuousOn.isOpen_inter_preimage hΩ isOpen_compl_singleton
  have hmeas : MeasurableSet (Ω ∩ Z) := by
    rw [← Set.diff_diff_right_self]
    exact hΩ.measurableSet.diff hW.measurableSet

  have hint : IntegrableOn (fun z => ‖(fun _ => (1 : ℂ)) z‖ ^ 2) (Ω \ Z) := by
    simp only [norm_one, one_pow]
    exact integrableOn_const ((measure_mono diff_subset).trans_lt measure_ball_lt_top).ne
  have hwk := extWeak n Ω F (fun _ => 1) hΩ hF (differentiableOn_const 1) hint
  obtain ⟨U, hU, hae⟩ := reg n Ω _ hΩ hwk
  have hae1 : (fun _ => (1 : ℂ)) =ᵐ[volume.restrict (Ω \ Z)] U := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset diff_subset hae,
      ae_restrict_mem hW.measurableSet] with z hz hzW
    rw [← hz, Set.indicator_of_mem hzW]
  have hEq1 : EqOn (fun _ => (1 : ℂ)) U (Ω \ Z) :=
    Measure.eqOn_open_of_ae_eq hae1 hW continuousOn_const (hU.continuousOn.mono diff_subset)
  have hz0W : z0 ∈ Ω \ Z := ⟨hz0, hFz0⟩

  have hUall : EqOn U (fun _ => (1 : ℂ)) Ω := by
    intro z hz
    set L : ℂ → V n := fun t => z0 + t • (z - z0) with hLdef
    set S : Set ℂ := L ⁻¹' Ω with hSdef
    have hLd : Differentiable ℂ L :=
      (differentiable_const _).add (differentiable_id.smul_const _)
    have hLc : Continuous L := hLd.continuous
    have hSo : IsOpen S := hΩ.preimage hLc
    have hSconv : Convex ℝ S := by
      intro t1 ht1 t2 ht2 a b ha hb hab
      have hm := (convex_ball c R) ht1 ht2 ha hb hab
      show z0 + (a • t1 + b • t2) • (z - z0) ∈ Ω
      have e : z0 + (a • t1 + b • t2) • (z - z0) =
          a • (z0 + t1 • (z - z0)) + b • (z0 + t2 • (z - z0)) := by
        calc z0 + (a • t1 + b • t2) • (z - z0)
            = (a + b) • z0 + (a • (t1 • (z - z0)) + b • (t2 • (z - z0))) := by
              rw [hab, one_smul, add_smul, smul_assoc, smul_assoc]
          _ = a • (z0 + t1 • (z - z0)) + b • (z0 + t2 • (z - z0)) := by
              rw [add_smul, smul_add, smul_add]
              abel
      rw [e]
      exact hm
    have hga : AnalyticOnNhd ℂ (U ∘ L) S :=
      (hU.comp hLd.differentiableOn fun t ht => ht).analyticOnNhd hSo
    have h0S : (0 : ℂ) ∈ S := by
      show z0 + (0 : ℂ) • (z - z0) ∈ Ω
      simpa using hz0
    have h1S : (1 : ℂ) ∈ S := by
      show z0 + (1 : ℂ) • (z - z0) ∈ Ω
      simpa using hz
    have hL0 : L 0 = z0 := by simp [hLdef]
    have hev : (U ∘ L) =ᶠ[𝓝 0] fun _ => (1 : ℂ) := by
      have hpre : L ⁻¹' (Ω \ Z) ∈ 𝓝 (0 : ℂ) :=
        hLc.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hW.mem_nhds hz0W)
      filter_upwards [hpre] with t ht using (hEq1 ht).symm
    have h1 := hga.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hSconv.isPreconnected
      h0S hev h1S
    simpa [hLdef] using h1

  have hZ : ∀ᵐ z ∂volume.restrict (Ω ∩ Z), False := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hae,
      ae_restrict_mem hmeas] with z hz hzZ
    rw [Set.indicator_of_notMem (fun h => h.2 hzZ.2), hUall hzZ.1] at hz
    exact zero_ne_one hz
  have h0 : volume.restrict (Ω ∩ Z) = 0 := ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hZ)
  exact Measure.restrict_eq_zero.1 h0

end ReciprocityTheory.L2DbarEstimates.C
