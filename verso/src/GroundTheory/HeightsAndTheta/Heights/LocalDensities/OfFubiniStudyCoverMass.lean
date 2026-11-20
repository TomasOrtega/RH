import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.HypImp
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.FourB

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

namespace OpenSetChart

variable {D : ℕ} {M : Set (Fin D → ℂ)}

open scoped Classical in

def retract (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) (y : Fin D → ℂ) : M :=
  ⟨if y ∈ M then y else x₀, by split_ifs with h; exacts [h, hx₀]⟩

/- English proof (translation)
Simplify using `[retract, hy]`.
-/
theorem retract_of_mem {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) {y : Fin D → ℂ} (hy : y ∈ M) :
    (retract x₀ hx₀ y : Fin D → ℂ) = y := by
  simp [retract, hy]

/- English proof (translation)
Unfold `retract`. Conclude with `(Measurable.ite hM.measurableSet measurable_id measurable_const).subtype_mk`.
-/
theorem measurable_retract (hM : IsOpen M) {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) :
    Measurable (retract x₀ hx₀) := by
  classical
  unfold retract
  exact (Measurable.ite hM.measurableSet measurable_id measurable_const).subtype_mk

def chart (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) : OpenPartialHomeomorph M (Fin D → ℂ) where
  toFun := Subtype.val
  invFun := retract x₀ hx₀
  source := Set.univ
  target := M
  map_source' x _ := x.2
  map_target' _ _ := Set.mem_univ _
  left_inv' x _ := Subtype.ext (retract_of_mem hx₀ x.2)
  right_inv' _ hy := retract_of_mem hx₀ hy
  open_source := isOpen_univ
  open_target := hM
  continuousOn_toFun := continuous_subtype_val.continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert (continuous_id : Continuous (id : M → M)) using 1
    funext y
    exact Subtype.ext (retract_of_mem hx₀ y.2)

/- English proof (translation)
The claim follows from `Filter.eventually_of_mem (hM.mem_nhds hy) fun _ hy' => retract_of_mem hx₀ hy'`.
-/
theorem eventuallyEq_retract (hM : IsOpen M) {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) {y : Fin D → ℂ}
    (hy : y ∈ M) : (fun y' => (retract x₀ hx₀ y' : Fin D → ℂ)) =ᶠ[𝓝 y] id :=
  Filter.eventually_of_mem (hM.mem_nhds hy) fun _ hy' => retract_of_mem hx₀ hy'

def atlas (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) : FinHolAtlas D M where
  n := 1
  chart _ := chart hM x₀ hx₀
  cover _ := ⟨0, Set.mem_univ _⟩
  holo _ _ := fun _ hy => analyticAt_id.congr (eventuallyEq_retract hM hx₀ hy.1).symm

def partition (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) :
    ChartPartition (atlas hM x₀ hx₀) where
  χ _ _ := 1
  smooth _ := fun _ => contDiffOn_const
  nonneg _ _ := zero_le_one
  tsupport_subset _ := fun _ _ => Set.mem_univ _
  sum_eq_one _ := by
    show ∑ _j : Fin 1, (1 : ℝ) = 1
    simp

/- English proof (translation)
Establish `hne : Nonempty (ChartPartition (atlas hM x₀ hx₀))` using `⟨partition hM x₀ hx₀⟩`. Establish `: Subsingleton (Fin (atlas hM x₀ hx₀).n)` using `(inferInstance : Subsingleton (Fin 1))`. Establish `hχ : ∀ j x, hne.some.χ j x = 1`. Introduce `j x`. Establish `h` using `hne.some.sum_eq_one x`.

Rewrite `h` using `[Fintype.sum_subsingleton _ j]`. Then use the resulting hypothesis. Set `j0 : Fin (atlas hM x₀ hx₀).n` to `⟨0, Nat.zero_lt_one⟩`. Establish `ht : ((atlas hM x₀ hx₀).chart j0).target = M` using `rfl`. Establish `hm : Measurable ((atlas hM x₀ hx₀).chart j0).symm` using `measurable_retract hM hx₀`. Rewrite using `[maMeasure, dif_pos hne, Fintype.sum_subsingleton _ j0, Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ht]`.

Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Rewrite using `[hχ, one_mul]`. Both sides reduce to the same expression.
-/
theorem maMeasure_univ (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) (u : M → ℝ) :
    maMeasure (atlas hM x₀ hx₀) (fun _ => LocPot.ofFun u) Set.univ =
      ∫⁻ y in M, ENNReal.ofReal (maDens (fun _ y' => u (retract x₀ hx₀ y')) y) := by
  have hne : Nonempty (ChartPartition (atlas hM x₀ hx₀)) := ⟨partition hM x₀ hx₀⟩
  have : Subsingleton (Fin (atlas hM x₀ hx₀).n) := (inferInstance : Subsingleton (Fin 1))
  have hχ : ∀ j x, hne.some.χ j x = 1 := by
    intro j x
    have h := hne.some.sum_eq_one x
    rwa [Fintype.sum_subsingleton _ j] at h
  let j0 : Fin (atlas hM x₀ hx₀).n := ⟨0, Nat.zero_lt_one⟩
  have ht : ((atlas hM x₀ hx₀).chart j0).target = M := rfl
  have hm : Measurable ((atlas hM x₀ hx₀).chart j0).symm := measurable_retract hM hx₀
  rw [maMeasure, dif_pos hne, Fintype.sum_subsingleton _ j0,
    Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ht]
  refine lintegral_congr fun y => ?_
  rw [hχ, one_mul]
  rfl

end OpenSetChart

open OpenSetChart

/- English proof (translation)
Establish `hH : ∀ i, hessC (φ i) y = hessC (ψ i) y`. Introduce `i`. Establish `h1 : fderiv ℝ (φ i) =ᶠ[𝓝 y] fderiv ℝ (ψ i)` using `(h i).fderiv`. Unfold `hessC`. Rewrite using `[h1.fderiv_eq]`.

Unfold `maDens`. Simplify using `only [hH]`.
-/
theorem maDens_congr_germ' {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 y] ψ i) : maDens φ y = maDens ψ y := by
  have hH : ∀ i, hessC (φ i) y = hessC (ψ i) y := by
    intro i
    have h1 : fderiv ℝ (φ i) =ᶠ[𝓝 y] fderiv ℝ (ψ i) := (h i).fderiv
    unfold hessC
    rw [h1.fderiv_eq]
  unfold maDens
  simp only [hH]

/- English proof (translation)
Introduce `D M Z z δ hB`. Take `⟨hM, hZ, hz, hmaps, hcov, hfib⟩` from `hB`. Break down `M.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩` into its components or cases. Establish `hZc : Zᶜ.Nonempty`. Assume the negation of the conclusion as `h`.

Rewrite `h` using `[Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff]`. Rewrite `hZ` using `[h, Measure.measure_univ_eq_zero]`. Conclude with `NeZero.ne (volume : Measure (Fin D → ℂ)) hZ`. Take `⟨w, hw⟩` from `hZc`. Establish `h1` using `hfib w hw`.

Establish `h0 : {x | x ∈ (∅ : Set (Fin D → ℂ)) ∧ z x = w} = ∅` using `by simp`. Rewrite `h1` using `[h0, Set.encard_empty]`. Establish `hδ : δ = 0` using `by exact_mod_cast h1.symm`. Substitute `hδ` using the available equality. Simplify using the standard rewrite rules.

Establish `hδ : δ ≠ 0`. Introduce `h0`. Establish `h1` using `hfib (z x₀) (hmaps hx₀)`. Establish `hmem : x₀ ∈ {x | x ∈ M ∧ z x = z x₀}` using `⟨hx₀, rfl⟩`. Rewrite `h1` using `[h0, Nat.cast_zero, Set.encard_eq_zero]`.

Rewrite `hmem` using `[h1]`. Conclude with `hmem`. Establish `hZcl : IsClosed Z`. Rewrite using `[← isOpen_compl_iff, isOpen_iff_forall_mem_open]`. Introduce `w hw`.

Take `⟨-, U, hwU, hU, -, H, hH⟩` from `hcov w hw`. Choose the witnesses or unpack the hypotheses as in `⟨x, hxM, hxw⟩ : {x | x ∈ M ∧ z x = w}.Nonempty := by`. Rewrite using `[← Set.encard_pos, hfib w hw]`. Conclude with `Nat.pos_of_ne_zero hδ` after adjusting the coercions. Set `i : (fun x : M => z x) ⁻¹' {w}` to `⟨⟨x, hxM⟩, hxw⟩`.

Use `⟨U, fun v hv => ?_, hU, hwU⟩` and prove the remaining obligations. Establish `h1 : v = z (H.symm (⟨v, hv⟩, i)).1`. Simplify using `using hH (H.symm (⟨v, hv⟩, i))`. Rewrite using `[h1]`. Conclude with `hmaps (H.symm (⟨v, hv⟩, i)).1.2`.

Establish `han : ∀ i, AnalyticOnNhd ℂ (fun y => z y i) M` using `fun i => ReciprocityTheory.AnForm.Osgood.osgood D M _ hM (differentiableOn_pi.1 hz i)`. Set `A` to `atlas hM x₀ hx₀`. Set `q : M → Fin D → ℂ` to `fun x => z x`. Set `u : M → ℝ` to `fun x => (1 / 2) * Real.log (1 + ∑ i, ‖q x i‖ ^ 2)`. Establish `hsm : ContDiffOn ℝ ∞ (fun y => (1 / 2) * Real.log (1 + ∑ i, ‖z y i‖ ^ 2)) M`.

Use `contDiffOn_const.mul (ContDiffOn.log (contDiffOn_const.add (ContDiffOn.sum fun i _ => (contDiff_norm_sq ℝ).comp_contDiffOn (((han i).contDiffOn hM.uniqueDiffOn).restrict_scalars ℝ))) fun y _ => ?_)` and prove the remaining obligations. Check the signs of the components of the expression. Establish `hu : A.Smooth u`. Introduce `j`. Use `(hsm.mono Set.inter_subset_left).congr fun y hy => ?_` and prove the remaining obligations.

Use `show u (retract x₀ hx₀ y) = _`. Simplify using `only [u, q, retract_of_mem hx₀ hy.1]`. Establish `hHyp : FubiniStudyCoverMass.Hyp A (LocPot.ofFun u) q Set.univ Z δ`. Use `⟨isPotential_ofFun A u hu, isOpen_univ, ?_, ?_, ?_, hZcl, hZ, ⟨fun x _ => hmaps x.2, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`.

Use `⟨Set.univ, isOpen_univ, Set.mem_univ _, 1, fun _ _ => 1, fun _ _ => analyticOnNhd_const, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Introduce `i j y hy`.

Conclude with `((han i) y hy.1).congr (((eventuallyEq_retract hM hx₀ hy.1).fun_comp fun y' => z y' i).symm)`. Establish `hpre : (Set.univ : Set M) = (fun x : M => z x) ⁻¹' Zᶜ`. Use extensionality with `x`. Simplify using `using hmaps x.2`. Conclude with `hcov.isCoveringMap_restrictPreimage.comp_homeomorph (Homeomorph.setCongr hpre)`.

Introduce `w hw`. Rewrite using `[← hfib w hw, ← Subtype.val_injective.encard_image]`. Use `congr 1`. Use extensionality with `y`. Simplify using `[q, and_comm]`.

Introduce `x y _`. Use `⟨Set.univ, isOpen_univ, Set.mem_univ _, 0, fun _ _ _ => analyticAt_const, ?_⟩` and prove the remaining obligations. Introduce `v _`. Simplify using `[LocPot.ofFun, u]`. Establish `key` using `(hA A (LocPot.ofFun u) q Set.univ Z δ hHyp).2`.

Rewrite `key` using `[maMeasure_univ]`. Rewrite using `[← key]`. Use `setLIntegral_congr_fun hM.measurableSet fun y hy => ?_` and prove the remaining obligations. Use `show ENNReal.ofReal (maDens _ y) = ENNReal.ofReal (maDens _ y)`. Use `congr 1`.

Use `maDens_congr_germ' fun _ => ?_` and prove the remaining obligations. Use `filter_upwards [hM.mem_nhds hy] with y' hy'`. Simplify using `only [u, q, retract_of_mem hx₀ hy']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem CoverMass2.of_fubiniStudyCoverMass (hA : FubiniStudyCoverMass.Statement) :
    IndefiniteRowSideFullHecke.FourB.CoverMass2.Statement := by
  intro D M Z z δ hB
  obtain ⟨hM, hZ, hz, hmaps, hcov, hfib⟩ := hB
  rcases M.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · have hZc : Zᶜ.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
      rw [h, Measure.measure_univ_eq_zero] at hZ
      exact NeZero.ne (volume : Measure (Fin D → ℂ)) hZ
    obtain ⟨w, hw⟩ := hZc
    have h1 := hfib w hw
    have h0 : {x | x ∈ (∅ : Set (Fin D → ℂ)) ∧ z x = w} = ∅ := by simp
    rw [h0, Set.encard_empty] at h1
    have hδ : δ = 0 := by exact_mod_cast h1.symm
    subst hδ
    simp
  ·
    have hδ : δ ≠ 0 := by
      intro h0
      have h1 := hfib (z x₀) (hmaps hx₀)
      have hmem : x₀ ∈ {x | x ∈ M ∧ z x = z x₀} := ⟨hx₀, rfl⟩
      rw [h0, Nat.cast_zero, Set.encard_eq_zero] at h1
      rw [h1] at hmem
      exact hmem

    have hZcl : IsClosed Z := by
      rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro w hw
      obtain ⟨-, U, hwU, hU, -, H, hH⟩ := hcov w hw
      obtain ⟨x, hxM, hxw⟩ : {x | x ∈ M ∧ z x = w}.Nonempty := by
        rw [← Set.encard_pos, hfib w hw]
        exact_mod_cast Nat.pos_of_ne_zero hδ
      let i : (fun x : M => z x) ⁻¹' {w} := ⟨⟨x, hxM⟩, hxw⟩
      refine ⟨U, fun v hv => ?_, hU, hwU⟩
      have h1 : v = z (H.symm (⟨v, hv⟩, i)).1 := by
        simpa using hH (H.symm (⟨v, hv⟩, i))
      rw [h1]
      exact hmaps (H.symm (⟨v, hv⟩, i)).1.2

    have han : ∀ i, AnalyticOnNhd ℂ (fun y => z y i) M := fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood D M _ hM (differentiableOn_pi.1 hz i)
    let A := atlas hM x₀ hx₀
    let q : M → Fin D → ℂ := fun x => z x
    let u : M → ℝ := fun x => (1 / 2) * Real.log (1 + ∑ i, ‖q x i‖ ^ 2)
    have hsm : ContDiffOn ℝ ∞ (fun y => (1 / 2) * Real.log (1 + ∑ i, ‖z y i‖ ^ 2)) M := by
      refine contDiffOn_const.mul (ContDiffOn.log (contDiffOn_const.add (ContDiffOn.sum
        fun i _ => (contDiff_norm_sq ℝ).comp_contDiffOn
          (((han i).contDiffOn hM.uniqueDiffOn).restrict_scalars ℝ))) fun y _ => ?_)
      positivity
    have hu : A.Smooth u := by
      intro j
      refine (hsm.mono Set.inter_subset_left).congr fun y hy => ?_
      show u (retract x₀ hx₀ y) = _
      simp only [u, q, retract_of_mem hx₀ hy.1]
    have hHyp : FubiniStudyCoverMass.Hyp A (LocPot.ofFun u) q Set.univ Z δ := by
      refine ⟨isPotential_ofFun A u hu, isOpen_univ, ?_, ?_, ?_, hZcl, hZ,
        ⟨fun x _ => hmaps x.2, ?_⟩, ?_, ?_⟩
      · intro x
        refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 1, fun _ _ => 1,
          fun _ _ => analyticOnNhd_const, ?_⟩
        ext y
        simp
      · simp
      · intro i j y hy
        exact ((han i) y hy.1).congr
          (((eventuallyEq_retract hM hx₀ hy.1).fun_comp fun y' => z y' i).symm)
      · have hpre : (Set.univ : Set M) = (fun x : M => z x) ⁻¹' Zᶜ := by
          ext x
          simpa using hmaps x.2
        exact hcov.isCoveringMap_restrictPreimage.comp_homeomorph (Homeomorph.setCongr hpre)
      · intro w hw
        rw [← hfib w hw, ← Subtype.val_injective.encard_image]
        congr 1
        ext y
        simp [q, and_comm]
      · intro x y _
        refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 0, fun _ _ _ => analyticAt_const, ?_⟩
        intro v _
        simp [LocPot.ofFun, u]
    have key := (hA A (LocPot.ofFun u) q Set.univ Z δ hHyp).2
    rw [maMeasure_univ] at key
    rw [← key]
    refine setLIntegral_congr_fun hM.measurableSet fun y hy => ?_
    show ENNReal.ofReal (maDens _ y) = ENNReal.ofReal (maDens _ y)
    congr 1
    refine maDens_congr_germ' fun _ => ?_
    filter_upwards [hM.mem_nhds hy] with y' hy'
    simp only [u, q, retract_of_mem hx₀ hy']
    ring

end GroundTheory.Heights₂.Heights.FourB
