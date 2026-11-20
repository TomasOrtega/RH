import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.Regular (RegChartData)

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

/- English proof (translation)
Establish `h : coordDiv S = ⋃ i ∈ S, {z : Fin e → ℂ | z i = 0}`. Use extensionality with `z`. Simplify using `[coordDiv]`. Rewrite using `[h]`. Conclude with `isClosed_biUnion_finset fun i _ => isClosed_eq (continuous_apply i) continuous_const`.
-/
theorem isClosed_coordDiv (S : Finset (Fin e)) : IsClosed (coordDiv S) := by
  have h : coordDiv S = ⋃ i ∈ S, {z : Fin e → ℂ | z i = 0} := by
    ext z
    simp [coordDiv]
  rw [h]
  exact isClosed_biUnion_finset fun i _ => isClosed_eq (continuous_apply i) continuous_const

/- English proof (translation)
Establish `h : coordDiv S = ⋃ i ∈ (S : Set (Fin e)), ((LinearMap.ker (LinearMap.proj i : (Fin e → ℂ) →ₗ[ℝ] ℂ) : Submodule ℝ (Fin e → ℂ)) : Set (Fin e → ℂ))`. Use extensionality with `z`. Simplify using `[coordDiv]`. Rewrite using `[h, measure_biUnion_null_iff S.countable_toSet]`. Introduce `i _`.

Apply `Measure.addHaar_submodule` to reduce the goal to its premises. Introduce `htop`. Establish `hmem : (Pi.single i (1 : ℂ) : Fin e → ℂ) ∈ LinearMap.ker (LinearMap.proj i : (Fin e → ℂ) →ₗ[ℝ] ℂ)`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`.

Simplify using `at hmem`.
-/
theorem volume_coordDiv_eq_zero (S : Finset (Fin e)) : volume (coordDiv S) = 0 := by
  have h : coordDiv S = ⋃ i ∈ (S : Set (Fin e)),
      ((LinearMap.ker (LinearMap.proj i : (Fin e → ℂ) →ₗ[ℝ] ℂ) : Submodule ℝ (Fin e → ℂ)) : Set (Fin e → ℂ)) := by
    ext z
    simp [coordDiv]
  rw [h, measure_biUnion_null_iff S.countable_toSet]
  intro i _
  apply Measure.addHaar_submodule
  intro htop
  have hmem : (Pi.single i (1 : ℂ) : Fin e → ℂ) ∈ LinearMap.ker (LinearMap.proj i : (Fin e → ℂ) →ₗ[ℝ] ℂ) := by
    rw [htop]
    exact Submodule.mem_top
  simp at hmem

/- English proof (translation)
Take `⟨j, hj⟩` from `R.cover x`. Conclude with `⟨j, R.closure_mid j (subset_closure (R.closure_inner j (subset_closure hj)))⟩`.
-/
theorem exists_mem_source (R : RegChartData A) (x : X) : ∃ j, x ∈ (R.chart j).source := by
  obtain ⟨j, hj⟩ := R.cover x
  exact ⟨j, R.closure_mid j (subset_closure (R.closure_inner j (subset_closure hj)))⟩

/- English proof (translation)
Establish `h : R.Yo = ⋃ j, (R.chart j).source ∩ (R.chart j) ⁻¹' (coordDiv (R.S j))ᶜ`. Use extensionality with `x`. Simplify using `only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Take `⟨j, hj⟩` from `exists_mem_source R x`. Conclude with `⟨j, hj, (R.mem_Yo j x hj).1 hx⟩`. Introduce and unpack `⟨j, hj, hc⟩`. Conclude with `(R.mem_Yo j x hj).2 hc`. Rewrite using `[h]`.

Conclude with `isOpen_iUnion fun j => (R.chart j).isOpen_inter_preimage (isClosed_coordDiv _).isOpen_compl`.
-/
theorem isOpen_Yo (R : RegChartData A) : IsOpen R.Yo := by
  have h : R.Yo = ⋃ j, (R.chart j).source ∩ (R.chart j) ⁻¹' (coordDiv (R.S j))ᶜ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := exists_mem_source R x
      exact ⟨j, hj, (R.mem_Yo j x hj).1 hx⟩
    · rintro ⟨j, hj, hc⟩
      exact (R.mem_Yo j x hj).2 hc
  rw [h]
  exact isOpen_iUnion fun j => (R.chart j).isOpen_inter_preimage (isClosed_coordDiv _).isOpen_compl

/- English proof (translation)
Establish `hsub : (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ ⊆ ⋃ k, ((A.chart j) ∘ (R.chart k).symm) '' (((R.chart k).target ∩ (R.chart k).symm ⁻¹' (A.chart j).source) ∩ coordDiv (R.S k))`. Introduce and unpack `y ⟨hyT, hyY⟩`. Establish `hxs : (A.chart j).symm y ∈ (A.chart j).source` using `(A.chart j).map_target hyT`. Take `⟨k, hk⟩` from `exists_mem_source R ((A.chart j).symm y)`. Establish `hxc : R.chart k ((A.chart j).symm y) ∈ coordDiv (R.S k)`.

Assume the negation of the conclusion as `h`. Conclude with `hyY ((R.mem_Yo k _ hk).2 h)`. Use `Set.mem_iUnion.mpr ⟨k, R.chart k ((A.chart j).symm y), ⟨⟨(R.chart k).map_source hk, ?_⟩, hxc⟩, ?_⟩` and prove the remaining obligations. Use `show (R.chart k).symm (R.chart k ((A.chart j).symm y)) ∈ (A.chart j).source`. Rewrite using `[(R.chart k).left_inv hk]`.

Conclude with `hxs`. Use `show (A.chart j) ((R.chart k).symm (R.chart k ((A.chart j).symm y))) = y`. Rewrite using `[(R.chart k).left_inv hk, (A.chart j).right_inv hyT]`. Use `measure_mono_null hsub (measure_iUnion_null fun k => ?_)` and prove the remaining obligations. Apply `MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` to reduce the goal to its premises.

Conclude with `(((R.compat k j).2.differentiableOn).restrictScalars ℝ).mono Set.inter_subset_left`. Conclude with `measure_mono_null Set.inter_subset_right (volume_coordDiv_eq_zero _)`.
-/
theorem volume_compl_Yo (R : RegChartData A) (j : Fin A.n) :
    volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ) = 0 := by
  have hsub : (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ ⊆
      ⋃ k, ((A.chart j) ∘ (R.chart k).symm) ''
        (((R.chart k).target ∩ (R.chart k).symm ⁻¹' (A.chart j).source) ∩ coordDiv (R.S k)) := by
    rintro y ⟨hyT, hyY⟩
    have hxs : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hyT
    obtain ⟨k, hk⟩ := exists_mem_source R ((A.chart j).symm y)
    have hxc : R.chart k ((A.chart j).symm y) ∈ coordDiv (R.S k) := by
      by_contra h
      exact hyY ((R.mem_Yo k _ hk).2 h)
    refine Set.mem_iUnion.mpr ⟨k, R.chart k ((A.chart j).symm y), ⟨⟨(R.chart k).map_source hk, ?_⟩, hxc⟩, ?_⟩
    · show (R.chart k).symm (R.chart k ((A.chart j).symm y)) ∈ (A.chart j).source
      rw [(R.chart k).left_inv hk]
      exact hxs
    · show (A.chart j) ((R.chart k).symm (R.chart k ((A.chart j).symm y))) = y
      rw [(R.chart k).left_inv hk, (A.chart j).right_inv hyT]
  refine measure_mono_null hsub (measure_iUnion_null fun k => ?_)
  apply MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
  · exact (((R.compat k j).2.differentiableOn).restrictScalars ℝ).mono Set.inter_subset_left
  · exact measure_mono_null Set.inter_subset_right (volume_coordDiv_eq_zero _)

/- English proof (translation)
Introduce `x hx`. Take `⟨k, hk⟩` from `exists_mem_source R x`. Establish `hxc : R.chart k x ∉ coordDiv (R.S k)` using `(R.mem_Yo k x hk).1 hx`. Establish `hUo : IsOpen ((R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ)` using `(R.chart k).isOpen_inter_preimage (isClosed_coordDiv _).isOpen_compl`. Establish `hxU : x ∈ (R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ` using `⟨hk, hxc⟩`.

Establish `hg : ContinuousOn (fun y : Fin e → ℂ => Real.exp 1 + R.f k y + ∑ i ∈ R.S k, Real.log (‖y i‖ ^ 2)⁻¹) ((R.chart k).target \ coordDiv (R.S k))`. Use `ContinuousOn.add (continuousOn_const.add ((R.f_smooth k).continuousOn.mono Set.sdiff_subset)) ?_` and prove the remaining obligations. Use `continuousOn_finsetSum _ fun i hi => ?_` and prove the remaining obligations. Establish `hne : ∀ y ∈ (R.chart k).target \ coordDiv (R.S k), ‖y i‖ ^ 2 ≠ 0`. Introduce `y hy`.

Establish `hyi : y i ≠ 0` using `fun h0 => hy.2 (show ∃ i' ∈ R.S k, y i' = 0 from ⟨i, hi, h0⟩)`. Conclude with `pow_ne_zero 2 (norm_ne_zero_iff.mpr hyi)`. Conclude with `(((continuous_apply i).norm.pow 2).continuousOn.inv₀ hne).log fun y hy => inv_ne_zero (hne y hy)`. Establish `heq : Set.EqOn R.r ((fun y : Fin e → ℂ => Real.exp 1 + R.f k y + ∑ i ∈ R.S k, Real.log (‖y i‖ ^ 2)⁻¹) ∘ R.chart k) ((R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ)`. Introduce `z hz`.

Establish `h1` using `R.r_chart k (R.chart k z) ⟨(R.chart k).map_source hz.1, hz.2⟩`. Rewrite `h1` using `[(R.chart k).left_inv hz.1]`. Conclude with `h1`. Establish `hcont` using `hg.comp ((R.chart k).continuousOn.mono Set.inter_subset_left) (fun z hz => ⟨(R.chart k).map_source hz.1, hz.2⟩)`. Conclude with `((hcont.congr heq).continuousAt (hUo.mem_nhds hxU)).continuousWithinAt`.
-/
theorem continuousOn_r (R : RegChartData A) : ContinuousOn R.r R.Yo := by
  intro x hx
  obtain ⟨k, hk⟩ := exists_mem_source R x
  have hxc : R.chart k x ∉ coordDiv (R.S k) := (R.mem_Yo k x hk).1 hx
  have hUo : IsOpen ((R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ) :=
    (R.chart k).isOpen_inter_preimage (isClosed_coordDiv _).isOpen_compl
  have hxU : x ∈ (R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ := ⟨hk, hxc⟩
  have hg : ContinuousOn (fun y : Fin e → ℂ => Real.exp 1 + R.f k y + ∑ i ∈ R.S k, Real.log (‖y i‖ ^ 2)⁻¹)
      ((R.chart k).target \ coordDiv (R.S k)) := by
    refine ContinuousOn.add (continuousOn_const.add ((R.f_smooth k).continuousOn.mono Set.sdiff_subset)) ?_
    refine continuousOn_finsetSum _ fun i hi => ?_
    have hne : ∀ y ∈ (R.chart k).target \ coordDiv (R.S k), ‖y i‖ ^ 2 ≠ 0 := by
      intro y hy
      have hyi : y i ≠ 0 := fun h0 => hy.2 (show ∃ i' ∈ R.S k, y i' = 0 from ⟨i, hi, h0⟩)
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hyi)
    exact (((continuous_apply i).norm.pow 2).continuousOn.inv₀ hne).log fun y hy => inv_ne_zero (hne y hy)
  have heq : Set.EqOn R.r ((fun y : Fin e → ℂ => Real.exp 1 + R.f k y + ∑ i ∈ R.S k, Real.log (‖y i‖ ^ 2)⁻¹) ∘ R.chart k)
      ((R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ) := by
    intro z hz
    have h1 := R.r_chart k (R.chart k z) ⟨(R.chart k).map_source hz.1, hz.2⟩
    rw [(R.chart k).left_inv hz.1] at h1
    exact h1
  have hcont := hg.comp ((R.chart k).continuousOn.mono Set.inter_subset_left)
    (fun z hz => ⟨(R.chart k).map_source hz.1, hz.2⟩)
  exact ((hcont.congr heq).continuousAt (hUo.mem_nhds hxU)).continuousWithinAt

/- English proof (translation)
Take `⟨k, hk⟩` from `exists_mem_source R x`. Establish `hxc : R.chart k x ∈ coordDiv (R.S k)`. Assume the negation of the conclusion as `h`. Conclude with `hx ((R.mem_Yo k x hk).2 h)`. Take `⟨i, hi, hi0⟩ : ∃ i ∈ R.S k, R.chart k x i = 0` from `hxc`.

Take `⟨B, hB⟩` from `R.f_bdd`. Establish `hca : ContinuousAt (fun z => ‖R.chart k z i‖ ^ 2) x` using `((continuous_apply i).continuousAt.comp ((R.chart k).continuousAt hk)).norm.pow 2`. Establish `h0 : ‖R.chart k x i‖ ^ 2 < Real.exp (-(l - Real.exp 1 + B))`. Rewrite using `[hi0, norm_zero]`. Simplify using `[Real.exp_pos]`.

Establish `h1 : ∀ᶠ z in 𝓝 x, ‖R.chart k z i‖ ^ 2 < Real.exp (-(l - Real.exp 1 + B))` using `Filter.Tendsto.eventually hca (gt_mem_nhds h0)`. Establish `h2 : ∀ᶠ z in 𝓝 x, z ∈ (R.chart k).source` using `(R.chart k).open_source.mem_nhds hk`. Use `filter_upwards [h1, h2] with z hz1 hz2`. Introduce and unpack `⟨hzY, hzr⟩`. Establish `hzc : R.chart k z ∉ coordDiv (R.S k)` using `(R.mem_Yo k z hz2).1 hzY`.

Establish `hyT : R.chart k z ∈ (R.chart k).target` using `(R.chart k).map_source hz2`. Establish `hr` using `R.r_chart k (R.chart k z) ⟨hyT, hzc⟩`. Rewrite `hr` using `[(R.chart k).left_inv hz2]`. Establish `hball : ‖R.chart k z‖ < 1` using `by simpa using R.target_subset k hyT`. Establish `hne : ∀ i' ∈ R.S k, R.chart k z i' ≠ 0` using `fun i' hi' h0 => hzc (show ∃ i'' ∈ R.S k, R.chart k z i'' = 0 from ⟨i', hi', h0⟩)`.

Establish `hterm : ∀ i' ∈ R.S k, 0 ≤ Real.log (‖R.chart k z i'‖ ^ 2)⁻¹`. Introduce `i' hi'`. Apply `Real.log_nonneg` to reduce the goal to its premises. Establish `hp : 0 < ‖R.chart k z i'‖` using `norm_pos_iff.mpr (hne i' hi')`. Establish `hlt : ‖R.chart k z i'‖ < 1` using `lt_of_le_of_lt (norm_le_pi_norm _ i') hball`.

Conclude with `(one_le_inv₀ (by positivity)).mpr (by nlinarith)`. Establish `hsum : Real.log (‖R.chart k z i‖ ^ 2)⁻¹ ≤ ∑ i' ∈ R.S k, Real.log (‖R.chart k z i'‖ ^ 2)⁻¹` using `Finset.single_le_sum hterm hi`. Establish `hp : 0 < ‖R.chart k z i‖ ^ 2`. Use `norm_pos_iff.mpr (hne i hi)` as an intermediate fact. Check the signs of the components of the expression.

Establish `hlog : Real.log (‖R.chart k z i‖ ^ 2) < -(l - Real.exp 1 + B)` using `(Real.log_lt_iff_lt_exp hp).mpr hz1`. Rewrite `hsum` using `[Real.log_inv]`. Establish `hf` using `(abs_le.mp (hB k _ hyT)).1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eventually_not_le_of_not_mem_Yo (R : RegChartData A) {x : X} (hx : x ∉ R.Yo) (l : ℝ) :
    ∀ᶠ z in 𝓝 x, ¬ (z ∈ R.Yo ∧ R.r z ≤ l) := by
  obtain ⟨k, hk⟩ := exists_mem_source R x
  have hxc : R.chart k x ∈ coordDiv (R.S k) := by
    by_contra h
    exact hx ((R.mem_Yo k x hk).2 h)
  obtain ⟨i, hi, hi0⟩ : ∃ i ∈ R.S k, R.chart k x i = 0 := hxc
  obtain ⟨B, hB⟩ := R.f_bdd
  have hca : ContinuousAt (fun z => ‖R.chart k z i‖ ^ 2) x :=
    ((continuous_apply i).continuousAt.comp ((R.chart k).continuousAt hk)).norm.pow 2
  have h0 : ‖R.chart k x i‖ ^ 2 < Real.exp (-(l - Real.exp 1 + B)) := by
    rw [hi0, norm_zero]
    simp [Real.exp_pos]
  have h1 : ∀ᶠ z in 𝓝 x, ‖R.chart k z i‖ ^ 2 < Real.exp (-(l - Real.exp 1 + B)) :=
    Filter.Tendsto.eventually hca (gt_mem_nhds h0)
  have h2 : ∀ᶠ z in 𝓝 x, z ∈ (R.chart k).source := (R.chart k).open_source.mem_nhds hk
  filter_upwards [h1, h2] with z hz1 hz2
  rintro ⟨hzY, hzr⟩
  have hzc : R.chart k z ∉ coordDiv (R.S k) := (R.mem_Yo k z hz2).1 hzY
  have hyT : R.chart k z ∈ (R.chart k).target := (R.chart k).map_source hz2
  have hr := R.r_chart k (R.chart k z) ⟨hyT, hzc⟩
  rw [(R.chart k).left_inv hz2] at hr
  have hball : ‖R.chart k z‖ < 1 := by simpa using R.target_subset k hyT
  have hne : ∀ i' ∈ R.S k, R.chart k z i' ≠ 0 := fun i' hi' h0 =>
    hzc (show ∃ i'' ∈ R.S k, R.chart k z i'' = 0 from ⟨i', hi', h0⟩)
  have hterm : ∀ i' ∈ R.S k, 0 ≤ Real.log (‖R.chart k z i'‖ ^ 2)⁻¹ := by
    intro i' hi'
    apply Real.log_nonneg
    have hp : 0 < ‖R.chart k z i'‖ := norm_pos_iff.mpr (hne i' hi')
    have hlt : ‖R.chart k z i'‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm _ i') hball
    exact (one_le_inv₀ (by positivity)).mpr (by nlinarith)
  have hsum : Real.log (‖R.chart k z i‖ ^ 2)⁻¹ ≤ ∑ i' ∈ R.S k, Real.log (‖R.chart k z i'‖ ^ 2)⁻¹ :=
    Finset.single_le_sum hterm hi
  have hp : 0 < ‖R.chart k z i‖ ^ 2 := by
    have := norm_pos_iff.mpr (hne i hi)
    positivity
  have hlog : Real.log (‖R.chart k z i‖ ^ 2) < -(l - Real.exp 1 + B) := (Real.log_lt_iff_lt_exp hp).mpr hz1
  rw [Real.log_inv] at hsum
  have hf := (abs_le.mp (hB k _ hyT)).1
  linarith

/- English proof (translation)
Use `IsClosed.isCompact (isOpen_compl_iff.mp (isOpen_iff_eventually.mpr fun x hx => ?_))` and prove the remaining obligations. Distinguish the cases in `hY : x ∈ R.Yo`. Establish `hlt : l < R.r x` using `not_le.mp fun h => hx ⟨hY, h⟩`. Establish `hcont : ContinuousAt R.r x` using `(continuousOn_r R).continuousAt ((isOpen_Yo R).mem_nhds hY)`. Use `filter_upwards [Filter.Tendsto.eventually hcont (lt_mem_nhds hlt)] with z hz`.

Simplify using `only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_le]`. Conclude with `fun _ => hz`. Conclude with `eventually_not_le_of_not_mem_Yo R hY l`.
-/
theorem isCompact_sublevel [CompactSpace X] (R : RegChartData A) (l : ℝ) :
    IsCompact {x | x ∈ R.Yo ∧ R.r x ≤ l} := by
  refine IsClosed.isCompact (isOpen_compl_iff.mp (isOpen_iff_eventually.mpr fun x hx => ?_))
  by_cases hY : x ∈ R.Yo
  · have hlt : l < R.r x := not_le.mp fun h => hx ⟨hY, h⟩
    have hcont : ContinuousAt R.r x := (continuousOn_r R).continuousAt ((isOpen_Yo R).mem_nhds hY)
    filter_upwards [Filter.Tendsto.eventually hcont (lt_mem_nhds hlt)] with z hz
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_le]
    exact fun _ => hz
  · exact eventually_not_le_of_not_mem_Yo R hY l

/- English proof (translation)
Introduce `e X _ _ _ A R`. Conclude with `⟨isOpen_Yo R, volume_compl_Yo R, continuousOn_r R, isCompact_sublevel R⟩`.
-/
theorem regData_open_part : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A),
    IsOpen R.Yo ∧ (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ) = 0) ∧
      ContinuousOn R.r R.Yo ∧ ∀ ℓ : ℝ, IsCompact {x | x ∈ R.Yo ∧ R.r x ≤ ℓ} := by
  intro e X _ _ _ A R
  exact ⟨isOpen_Yo R, volume_compl_Yo R, continuousOn_r R, isCompact_sublevel R⟩

end GlobalTheory.CompanionTheory.Ar.Giv
