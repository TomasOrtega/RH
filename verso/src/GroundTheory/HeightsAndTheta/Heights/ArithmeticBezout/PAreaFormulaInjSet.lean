import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsAreaFormulaInjSet
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsAreaFormulaLocal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionFormula
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetImageAreaSetFrame
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set

open scoped ENNReal

/- English proof (translation)
Introduce `E F _ _ _ _ _ _ _ _ _ _ k hk U A f hU hf hAU hA hinj`. Use `set J : E → ℝ≥0∞ := fun x => ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) with hJdef`. Express the relevant statement in the definitionally equal form `μH[(k : ℝ)] (f '' A) = ∫⁻ x in A, J x ∂(μH[(k : ℝ)])`. Establish `hdiff : ∀ x ∈ U, HasFDerivAt f (fderiv ℝ f x) x` using `fun x hx => ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)).hasFDerivAt`. Use `set C : Set E := A ∩ fderiv ℝ f ⁻¹' {L : E →L[ℝ] F | Function.Injective L}ᶜ with hCdef`.

Establish `hCm : MeasurableSet C` using `hA.inter (measurable_fderiv ℝ f ContinuousLinearMap.isOpen_injective.measurableSet.compl)`. Establish `hJC : EqOn J (fun _ => 0) C`. Introduce `x hx`. Establish `hni : ¬ Function.Injective (fderiv ℝ f x : E →ₗ[ℝ] F)` using `hx.2`. Establish `h0 : (fderiv ℝ f x : E →ₗ[ℝ] F).normDet = 0` using `LinearMap.normDet_eq_zero_iff_ker_ne_bot.2 fun hk0 => hni (LinearMap.ker_eq_bot.1 hk0)`.

Simplify using `[hJdef, SheetImageAreaSet.areaJacobian_eq_normDet, h0]`. Establish `hCnull : μH[(k : ℝ)] (f '' C) = 0`. Set `e : (Fin k → ℝ) ≃L[ℝ] E` to `(finBasisOfFinrankEq ℝ E hk).equivFun.symm.toContinuousLinearEquiv`. Establish `himg : f '' C = (f ∘ e) '' (e ⁻¹' C)`. Rewrite using `[image_comp, image_preimage_eq _ e.surjective]`.

Establish `key` using `IndefiniteRowSideFullHecke.ComplexSets.hausdorffMeasure_image_eq_zero_of_not_injective (f := f ∘ e) (s := e ⁻¹' C) (f' := fun x => (fderiv ℝ f (e x)).comp (e : (Fin k → ℝ) →L[ℝ] E)) ?_ ?_`. Rewrite using `[himg]`. Simplify using `using key`. Introduce `x hx`. Conclude with `((hdiff (e x) (hAU hx.1)).comp x e.hasFDerivAt).hasFDerivWithinAt`.

Introduce `x hx hinj'`. Apply `hx.2` to reduce the goal to its premises. Introduce `a c hac`. Establish `h2` using `@hinj' (e.symm a) (e.symm c) (by simpa using hac)`. Simplify using `using congrArg e h2`.

Use `set R : Set E := A \ C with hRdef`. Establish `hRm : MeasurableSet R` using `hA.diff hCm`. Use `set G : Set (Set E) := {V | IsOpen V ∧ V ⊆ U ∧ ∀ B ⊆ V, MeasurableSet B → μH[(k : ℝ)] (f '' B) = ∫⁻ x in B, J x ∂(μH[(k : ℝ)])} with hGdef`. Establish `hRG : R ⊆ ⋃₀ G`. Introduce `x hx`.

Establish `hxinj : Function.Injective (fderiv ℝ f x)`. Assume the negation of the conclusion as `hn`. Conclude with `hx.2 ⟨hx.1, hn⟩`. Take `⟨V, hVo, hxV, hVU, hV⟩` from `h E F k hk U f x hU hf (hAU hx.1) hxinj`. Conclude with `⟨V, ⟨hVo, hVU, hV⟩, hxV⟩`.

Take `⟨T, hTc, hTG, hTU⟩` from `TopologicalSpace.isOpen_sUnion_countable G fun V hV => hV.1`. Establish `hG0 : (∅ : Set E) ∈ G` using `⟨isOpen_empty, empty_subset _, fun B hB _ => by`. Rewrite using `[subset_empty_iff.1 hB]`. Use the proof step `simp⟩`. Take `⟨V, hVeq⟩` from `(hTc.insert ∅).exists_eq_range (insert_nonempty _ _)`.

Establish `hVG : ∀ n, V n ∈ G`. Introduce `n`. Establish `hn : V n ∈ insert ∅ T`. Rewrite using `[hVeq]`. Conclude with `mem_range_self n`.

Break down `hn with h0 | hT` into its components or cases. Rewrite using `[h0]`. Conclude with `hG0`. Conclude with `hTG hT`. Establish `hRV : R ⊆ ⋃ n, V n`.

Introduce `x hx`. Establish `hx' : x ∈ ⋃₀ T`. Rewrite using `[hTU]`. Conclude with `hRG hx`. Take `⟨W, hWT, hxW⟩` from `hx'`.

Establish `hW : W ∈ range V`. Rewrite using `[← hVeq]`. Conclude with `mem_insert_of_mem _ hWT`. Take `⟨n, rfl⟩` from `hW`. Conclude with `mem_iUnion.2 ⟨n, hxW⟩`.

Use `set B : ℕ → Set E := fun n => R ∩ disjointed V n with hBdef`. Establish `hBm : ∀ n, MeasurableSet (B n)` using `fun n => hRm.inter (MeasurableSet.disjointed (fun m => (hVG m).1.measurableSet) n)`. Establish `hBd : Pairwise (Function.onFun Disjoint B)` using `fun m n hmn => ((disjoint_disjointed V) hmn).mono inter_subset_right inter_subset_right`. Establish `hBU : ⋃ n, B n = R`. Rewrite using `[← inter_iUnion, iUnion_disjointed]`.

Conclude with `inter_eq_left.2 hRV`. Establish `hBV : ∀ n, B n ⊆ V n` using `fun n => inter_subset_right.trans (disjointed_subset V n)`. Establish `hBA : ∀ n, B n ⊆ A` using `fun n => inter_subset_left.trans sdiff_subset`. Establish `hR : μH[(k : ℝ)] (f '' R) = ∫⁻ x in R, J x ∂(μH[(k : ℝ)])`. Rewrite using `[← hBU, image_iUnion, measure_iUnion, lintegral_iUnion hBm hBd]`.

Conclude with `tsum_congr fun n => (hVG n).2.2 (B n) (hBV n) (hBm n)`. Introduce `m n hmn`. Use `disjoint_left.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩ ⟨c, hc, hca⟩`. Take `rfl` from `hinj (hBA n hc) (hBA m ha) hca`.

Conclude with `disjoint_left.1 (hBd hmn) ha hc`. Introduce `n`. Conclude with `(hBm n).image_of_continuousOn_injOn (hf.continuousOn.mono ((hBV n).trans (hVG n).2.1)) (hinj.mono (hBA n))`. Establish `hAC : A = R ∪ C` using `(sdiff_union_of_subset inter_subset_left).symm`. Establish `himgA : μH[(k : ℝ)] (f '' A) = μH[(k : ℝ)] (f '' R)`.

Apply `le_antisymm` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← image_union, ← hAC]`. Use `_ ≤ μH[(k : ℝ)] (f '' R) + μH[(k : ℝ)] (f '' C) := measure_union_le _ _`. Use `_ = μH[(k : ℝ)] (f '' R) := by rw [hCnull, add_zero]`.

Conclude with `measure_mono (image_mono sdiff_subset)`. Establish `hintA : ∫⁻ x in A, J x ∂(μH[(k : ℝ)]) = ∫⁻ x in R, J x ∂(μH[(k : ℝ)])`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[setLIntegral_congr_fun hCm hJC, lintegral_zero, add_zero]`. Rewrite using `[himgA, hR, hintA]`.
-/
theorem AreaFormulaInjSet.proof (h : AreaFormulaLocal.Statement) : AreaFormulaInjSet.Statement := by
  classical
  intro E F _ _ _ _ _ _ _ _ _ _ k hk U A f hU hf hAU hA hinj
  set J : E → ℝ≥0∞ := fun x => ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) with hJdef
  change μH[(k : ℝ)] (f '' A) = ∫⁻ x in A, J x ∂(μH[(k : ℝ)])
  have hdiff : ∀ x ∈ U, HasFDerivAt f (fderiv ℝ f x) x := fun x hx =>
    ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)).hasFDerivAt

  set C : Set E := A ∩ fderiv ℝ f ⁻¹' {L : E →L[ℝ] F | Function.Injective L}ᶜ with hCdef
  have hCm : MeasurableSet C :=
    hA.inter (measurable_fderiv ℝ f ContinuousLinearMap.isOpen_injective.measurableSet.compl)
  have hJC : EqOn J (fun _ => 0) C := by
    intro x hx
    have hni : ¬ Function.Injective (fderiv ℝ f x : E →ₗ[ℝ] F) := hx.2
    have h0 : (fderiv ℝ f x : E →ₗ[ℝ] F).normDet = 0 :=
      LinearMap.normDet_eq_zero_iff_ker_ne_bot.2 fun hk0 => hni (LinearMap.ker_eq_bot.1 hk0)
    simp [hJdef, SheetImageAreaSet.areaJacobian_eq_normDet, h0]
  have hCnull : μH[(k : ℝ)] (f '' C) = 0 := by
    let e : (Fin k → ℝ) ≃L[ℝ] E := (finBasisOfFinrankEq ℝ E hk).equivFun.symm.toContinuousLinearEquiv
    have himg : f '' C = (f ∘ e) '' (e ⁻¹' C) := by
      rw [image_comp, image_preimage_eq _ e.surjective]
    have key := IndefiniteRowSideFullHecke.ComplexSets.hausdorffMeasure_image_eq_zero_of_not_injective (f := f ∘ e)
      (s := e ⁻¹' C) (f' := fun x => (fderiv ℝ f (e x)).comp (e : (Fin k → ℝ) →L[ℝ] E)) ?_ ?_
    · rw [himg]
      simpa using key
    · intro x hx
      exact ((hdiff (e x) (hAU hx.1)).comp x e.hasFDerivAt).hasFDerivWithinAt
    · intro x hx hinj'
      apply hx.2
      intro a c hac
      have h2 := @hinj' (e.symm a) (e.symm c) (by simpa using hac)
      simpa using congrArg e h2

  set R : Set E := A \ C with hRdef
  have hRm : MeasurableSet R := hA.diff hCm
  set G : Set (Set E) := {V | IsOpen V ∧ V ⊆ U ∧ ∀ B ⊆ V, MeasurableSet B →
    μH[(k : ℝ)] (f '' B) = ∫⁻ x in B, J x ∂(μH[(k : ℝ)])} with hGdef
  have hRG : R ⊆ ⋃₀ G := by
    intro x hx
    have hxinj : Function.Injective (fderiv ℝ f x) := by
      by_contra hn
      exact hx.2 ⟨hx.1, hn⟩
    obtain ⟨V, hVo, hxV, hVU, hV⟩ := h E F k hk U f x hU hf (hAU hx.1) hxinj
    exact ⟨V, ⟨hVo, hVU, hV⟩, hxV⟩
  obtain ⟨T, hTc, hTG, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable G fun V hV => hV.1
  have hG0 : (∅ : Set E) ∈ G := ⟨isOpen_empty, empty_subset _, fun B hB _ => by
    rw [subset_empty_iff.1 hB]
    simp⟩
  obtain ⟨V, hVeq⟩ := (hTc.insert ∅).exists_eq_range (insert_nonempty _ _)
  have hVG : ∀ n, V n ∈ G := by
    intro n
    have hn : V n ∈ insert ∅ T := by
      rw [hVeq]
      exact mem_range_self n
    rcases hn with h0 | hT
    · rw [h0]
      exact hG0
    · exact hTG hT
  have hRV : R ⊆ ⋃ n, V n := by
    intro x hx
    have hx' : x ∈ ⋃₀ T := by
      rw [hTU]
      exact hRG hx
    obtain ⟨W, hWT, hxW⟩ := hx'
    have hW : W ∈ range V := by
      rw [← hVeq]
      exact mem_insert_of_mem _ hWT
    obtain ⟨n, rfl⟩ := hW
    exact mem_iUnion.2 ⟨n, hxW⟩

  set B : ℕ → Set E := fun n => R ∩ disjointed V n with hBdef
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    hRm.inter (MeasurableSet.disjointed (fun m => (hVG m).1.measurableSet) n)
  have hBd : Pairwise (Function.onFun Disjoint B) := fun m n hmn =>
    ((disjoint_disjointed V) hmn).mono inter_subset_right inter_subset_right
  have hBU : ⋃ n, B n = R := by
    rw [← inter_iUnion, iUnion_disjointed]
    exact inter_eq_left.2 hRV
  have hBV : ∀ n, B n ⊆ V n := fun n => inter_subset_right.trans (disjointed_subset V n)
  have hBA : ∀ n, B n ⊆ A := fun n => inter_subset_left.trans sdiff_subset
  have hR : μH[(k : ℝ)] (f '' R) = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) := by
    rw [← hBU, image_iUnion, measure_iUnion, lintegral_iUnion hBm hBd]
    · exact tsum_congr fun n => (hVG n).2.2 (B n) (hBV n) (hBm n)
    · intro m n hmn
      refine disjoint_left.2 ?_
      rintro _ ⟨a, ha, rfl⟩ ⟨c, hc, hca⟩
      obtain rfl := hinj (hBA n hc) (hBA m ha) hca
      exact disjoint_left.1 (hBd hmn) ha hc
    · intro n
      exact (hBm n).image_of_continuousOn_injOn
        (hf.continuousOn.mono ((hBV n).trans (hVG n).2.1)) (hinj.mono (hBA n))

  have hAC : A = R ∪ C := (sdiff_union_of_subset inter_subset_left).symm
  have himgA : μH[(k : ℝ)] (f '' A) = μH[(k : ℝ)] (f '' R) := by
    apply le_antisymm
    · calc μH[(k : ℝ)] (f '' A) = μH[(k : ℝ)] (f '' R ∪ f '' C) := by
            rw [← image_union, ← hAC]
        _ ≤ μH[(k : ℝ)] (f '' R) + μH[(k : ℝ)] (f '' C) := measure_union_le _ _
        _ = μH[(k : ℝ)] (f '' R) := by rw [hCnull, add_zero]
    · exact measure_mono (image_mono sdiff_subset)
  have hintA : ∫⁻ x in A, J x ∂(μH[(k : ℝ)]) = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) := by
    calc ∫⁻ x in A, J x ∂(μH[(k : ℝ)]) = ∫⁻ x in R ∪ C, J x ∂(μH[(k : ℝ)]) := by rw [← hAC]
      _ = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) + ∫⁻ x in C, J x ∂(μH[(k : ℝ)]) :=
          lintegral_union hCm disjoint_sdiff_left
      _ = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) := by
          rw [setLIntegral_congr_fun hCm hJC, lintegral_zero, add_zero]
  rw [himgA, hR, hintA]

end GroundTheory.Heights₂.Heights
