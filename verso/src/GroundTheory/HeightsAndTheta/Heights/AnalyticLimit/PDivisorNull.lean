import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StDivisorNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Metric
open ReciprocityTheory.AnForm.A (coordDiv)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

variable {D : ℕ} {X : Type} [TopologicalSpace X]

/- English proof (translation)
Take `⟨j, hx, hW⟩` from `R.cover x`. Conclude with `⟨j, hx, R.closure_W'_subset j (subset_closure (R.closure_W''_subset j (subset_closure hW)))⟩`.
-/
theorem DivisorNull.exists_chart_mem_alt {A : FinHolAtlas D X} (R : RegChartData A) (x : X) :
    ∃ j, x ∈ (R.ψ j).source ∧ R.ψ j x ∈ R.W j := by
  obtain ⟨j, hx, hW⟩ := R.cover x
  exact ⟨j, hx, R.closure_W'_subset j (subset_closure (R.closure_W''_subset j (subset_closure hW)))⟩

/- English proof (translation)
Establish `h` using `R.mem_Yo_iff j _ hW`. Rewrite `h` using `[(R.ψ j).left_inv hy]`. Rewrite using `[h, not_not, Finset.prod_eq_zero_iff]`. Both sides reduce to the same expression.
-/
theorem DivisorNull.not_mem_Yo_iff {A : FinHolAtlas D X} (R : RegChartData A) (j : Fin R.n) {y : X}
    (hy : y ∈ (R.ψ j).source) (hW : R.ψ j y ∈ R.W j) :
    y ∉ R.Yo ↔ ∏ i ∈ R.S j, R.ψ j y i = 0 := by
  have h := R.mem_Yo_iff j _ hW
  rw [(R.ψ j).left_inv hy] at h
  rw [h, not_not, Finset.prod_eq_zero_iff]
  rfl

/- English proof (translation)
Introduce `x`. Take `⟨j, hx, hW⟩` from `DivisorNull.exists_chart_mem_alt R x`. Use `⟨(R.ψ j).source ∩ R.ψ j ⁻¹' R.W j, (R.ψ j).isOpen_inter_preimage (R.isOpen_kappaOpenNeighbourhood j), ⟨hx, hW⟩, 1, fun _ y => ∏ i ∈ R.S j, R.ψ j y i, ?_, ?_⟩` and prove the remaining obligations. Introduce `_ k`. Establish `hk` using `(R.compat j k).1`.

Use `show AnalyticOnNhd ℂ (fun z => ∏ i ∈ R.S j, (R.ψ j ∘ (A.chart k).symm) z i) _`. Use `Finset.analyticOnNhd_fun_prod _ fun i _ z hz => ?_` and prove the remaining obligations. Establish `hz' : AnalyticAt ℂ (R.ψ j ∘ (A.chart k).symm) z` using `hk z ⟨hz.1, hz.2.1⟩`. Conclude with `((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt _).comp hz'`. Use extensionality with `y`.

Simplify using `only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy, hs, hw⟩`. Conclude with `⟨⟨hs, hw⟩, fun _ => (DivisorNull.not_mem_Yo_iff R j hs hw).1 hy⟩`. Introduce and unpack `⟨⟨hs, hw⟩, h⟩`.

Conclude with `⟨(DivisorNull.not_mem_Yo_iff R j hs hw).2 (h 0), hs, hw⟩`.
-/
theorem DivisorNull.isAnalyticSubset_compl_Yo {A : FinHolAtlas D X} (R : RegChartData A) :
    A.IsAnalyticSubset R.Yoᶜ := by
  intro x
  obtain ⟨j, hx, hW⟩ := DivisorNull.exists_chart_mem_alt R x
  refine ⟨(R.ψ j).source ∩ R.ψ j ⁻¹' R.W j, (R.ψ j).isOpen_inter_preimage (R.isOpen_kappaOpenNeighbourhood j), ⟨hx, hW⟩,
    1, fun _ y => ∏ i ∈ R.S j, R.ψ j y i, ?_, ?_⟩
  · intro _ k
    have hk := (R.compat j k).1
    show AnalyticOnNhd ℂ (fun z => ∏ i ∈ R.S j, (R.ψ j ∘ (A.chart k).symm) z i) _
    refine Finset.analyticOnNhd_fun_prod _ fun i _ z hz => ?_
    have hz' : AnalyticAt ℂ (R.ψ j ∘ (A.chart k).symm) z := hk z ⟨hz.1, hz.2.1⟩
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt _).comp hz'
  · ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨hy, hs, hw⟩
      exact ⟨⟨hs, hw⟩, fun _ => (DivisorNull.not_mem_Yo_iff R j hs hw).1 hy⟩
    · rintro ⟨⟨hs, hw⟩, h⟩
      exact ⟨(DivisorNull.not_mem_Yo_iff R j hs hw).2 (h 0), hs, hw⟩

/- English proof (translation)
Use `Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_` and prove the remaining obligations. Take `⟨U, hUY, hU, hxU⟩` from `mem_interior.1 hx`. Take `⟨j, hxs, hW⟩` from `DivisorNull.exists_chart_mem_alt R x`. Establish `hO : IsOpen (R.W j ∩ (R.ψ j).symm ⁻¹' U)`. Establish `h2` using `((R.ψ j).isOpen_inter_preimage_symm hU).inter (R.isOpen_kappaOpenNeighbourhood j)`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz, hzU⟩`. Conclude with `⟨⟨R.W_subset j hz, hzU⟩, hz⟩`.

Introduce and unpack `⟨⟨_, hzU⟩, hz⟩`. Conclude with `⟨hz, hzU⟩`. Establish `hxO : R.ψ j x ∈ R.W j ∩ (R.ψ j).symm ⁻¹' U`. Use `⟨hW, ?_⟩` and prove the remaining obligations. Use `show (R.ψ j).symm (R.ψ j x) ∈ U`.

Rewrite using `[(R.ψ j).left_inv hxs]`. Conclude with `hxU`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hO _ hxO`. Set `w : Fin D → ℂ` to `fun i => if R.ψ j x i = 0 then ((ε / 2 : ℝ) : ℂ) else R.ψ j x i`. Establish `hw0 : ∀ i, w i ≠ 0`.

Introduce `i`. Distinguish the cases in `h : R.ψ j x i = 0`. Simplify using `only [w, if_pos h, ne_eq, Complex.ofReal_eq_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [w, if_neg h]`.

Conclude with `h`. Establish `hwb : w ∈ ball (R.ψ j x) ε`. Rewrite using `[mem_ball, dist_eq_norm, pi_norm_lt_iff hε]`. Introduce `i`. Distinguish the cases in `h : R.ψ j x i = 0`.

Rewrite using `[Pi.sub_apply]`. Simplify using `only [w]`. Rewrite using `[if_pos h, h, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [w, Pi.sub_apply, if_neg h, sub_self, norm_zero]`.

Conclude with `hε`. Take `⟨hwW, hwU⟩` from `hball hwb`. Establish `hsrc : (R.ψ j).symm w ∈ (R.ψ j).source` using `(R.ψ j).map_target (R.W_subset j hwW)`. Establish `hright : R.ψ j ((R.ψ j).symm w) = w` using `(R.ψ j).right_inv (R.W_subset j hwW)`. Establish `hprod` using `(DivisorNull.not_mem_Yo_iff R j hsrc (by rw [hright]; exact hwW)).1 (hUY hwU)`.

Rewrite `hprod` using `[hright, Finset.prod_eq_zero_iff]`. Take `⟨i, -, hi⟩` from `hprod`. Conclude with `hw0 i hi`.
-/
theorem DivisorNull.interior_compl_Yo {A : FinHolAtlas D X} (R : RegChartData A) :
    interior R.Yoᶜ = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨U, hUY, hU, hxU⟩ := mem_interior.1 hx
  obtain ⟨j, hxs, hW⟩ := DivisorNull.exists_chart_mem_alt R x
  have hO : IsOpen (R.W j ∩ (R.ψ j).symm ⁻¹' U) := by
    have h2 := ((R.ψ j).isOpen_inter_preimage_symm hU).inter (R.isOpen_kappaOpenNeighbourhood j)
    convert h2 using 1
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨⟨R.W_subset j hz, hzU⟩, hz⟩
    · rintro ⟨⟨_, hzU⟩, hz⟩
      exact ⟨hz, hzU⟩
  have hxO : R.ψ j x ∈ R.W j ∩ (R.ψ j).symm ⁻¹' U := by
    refine ⟨hW, ?_⟩
    show (R.ψ j).symm (R.ψ j x) ∈ U
    rw [(R.ψ j).left_inv hxs]
    exact hxU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO _ hxO
  let w : Fin D → ℂ := fun i => if R.ψ j x i = 0 then ((ε / 2 : ℝ) : ℂ) else R.ψ j x i
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i
    by_cases h : R.ψ j x i = 0
    · simp only [w, if_pos h, ne_eq, Complex.ofReal_eq_zero]
      linarith
    · simp only [w, if_neg h]
      exact h
  have hwb : w ∈ ball (R.ψ j x) ε := by
    rw [mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
    intro i
    by_cases h : R.ψ j x i = 0
    · rw [Pi.sub_apply]
      simp only [w]
      rw [if_pos h, h, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · simp only [w, Pi.sub_apply, if_neg h, sub_self, norm_zero]
      exact hε
  obtain ⟨hwW, hwU⟩ := hball hwb
  have hsrc : (R.ψ j).symm w ∈ (R.ψ j).source := (R.ψ j).map_target (R.W_subset j hwW)
  have hright : R.ψ j ((R.ψ j).symm w) = w := (R.ψ j).right_inv (R.W_subset j hwW)
  have hprod := (DivisorNull.not_mem_Yo_iff R j hsrc (by rw [hright]; exact hwW)).1 (hUY hwU)
  rw [hright, Finset.prod_eq_zero_iff] at hprod
  obtain ⟨i, -, hi⟩ := hprod
  exact hw0 i hi

/- English proof (translation)
Introduce `_ R` and use `⟨DivisorNull.isAnalyticSubset_compl_Yo R, DivisorNull.interior_compl_Yo R⟩`.
-/
theorem DivisorNull.proof : DivisorNull.Statement :=
  fun _ R => ⟨DivisorNull.isAnalyticSubset_compl_Yo R, DivisorNull.interior_compl_Yo R⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
