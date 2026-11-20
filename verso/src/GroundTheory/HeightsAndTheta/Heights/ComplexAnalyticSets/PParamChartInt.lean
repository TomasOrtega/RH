import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamChartInt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartIntCountAdd
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamPieceInt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamCritNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamOffRegularZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularInjectivePieces
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamDensIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

/- English proof (translation)
Introduce `n d W A σ r r' N hW hdim hA hσ hinj hN hrr hprop hcov f φ hf hfc hfN hφ`. Use `set F : (Fin d → ℂ) → ℝ := fun w => f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w with hF`. Establish `hf0 : ∀ x, x ∉ N → f x = 0` using `fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hfN h)`. Use `set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg`. Use `set Ω : Set (Fin d → ℂ) := Metric.ball 0 r ∩ σ ⁻¹' N with hΩ`.

Establish `hΩo : IsOpen Ω` using `hσ.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hN`. Establish `hmv : Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x)`. Establish `h` using `(Matrix.mulVecLin A).toContinuousLinearMap.differentiable`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`.

Simplify using the standard rewrite rules. Establish `hgd : DifferentiableOn ℂ g Ω` using `hmv.comp_differentiableOn (hσ.mono Set.inter_subset_left)`. Use `set Reg : Set (Fin d → ℂ) := {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} with hReg`. Take `⟨P, hPm, hPd, hPU, hPinj⟩` from `hRP d Ω g hΩo hgd`. Establish `hPReg : ⋃ i, P i = Reg`.

Rewrite using `[hPU]`. Use extensionality with `w`. Simplify using `only [hΩ, Reg, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, and_assoc]`. Establish `hPsub : ∀ i, P i ⊆ Reg` using `fun i => hPReg ▸ Set.subset_iUnion P i`. Establish `hRegB : Reg ⊆ Metric.ball 0 r` using `fun w hw => hw.1`.

Establish `hPB : ∀ i, P i ⊆ Metric.ball 0 r` using `fun i => (hPsub i).trans hRegB`. Establish `hσP : ∀ i, MeasurableSet (σ '' P i)` using `fun i => (hPm i).image_of_continuousOn_injOn (hσ.continuousOn.mono (hPB i)) (hinj.mono (hPB i))`. Establish `hσReg : σ '' Reg = ⋃ i, σ '' P i` using `by rw [← hPReg, Set.image_iUnion]`. Set `E : ℕ → Set (Fin n → ℂ)` to `fun i => Nat.casesOn i (σ '' Reg)ᶜ fun j => σ '' P j`. Establish `hEm : ∀ i, MeasurableSet (E i)`.

Introduce `i`. Consider the cases of `i with`. Consider the case `zero => show MeasurableSet (σ '' Reg)ᶜ`. Rewrite using `[hσReg]`. Conclude with `(MeasurableSet.iUnion hσP).compl`.

Consider the case `succ j => exact hσP j`. Establish `hdisjP : ∀ i j, i ≠ j → Disjoint (σ '' P i) (σ '' P j)`. Introduce `i j hij`. Use `Set.disjoint_left.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩`.

Establish `hba` using `hinj (hPB j hb) (hPB i ha) hab`. Substitute `hba` using the available equality. Conclude with `Set.disjoint_left.1 (hPd hij) ha hb`. Establish `hEd : Pairwise (Function.onFun Disjoint E)`. Introduce `i j hij`.

Consider the cases of `i with`. Consider the case `zero`. Consider the cases of `j with`. Consider the case `zero => exact absurd rfl hij`. Consider the case `succ j => exact Set.disjoint_compl_left_iff_subset.2 (Set.image_mono (hPsub j))`.

Consider the case `succ i`. Consider the cases of `j with`. Consider the case `zero => exact Set.disjoint_compl_right_iff_subset.2 (Set.image_mono (hPsub i))`. Consider the case `succ j => exact hdisjP i j fun h => hij (by rw [h])`. Establish `hEU : ⋃ i, E i = Set.univ`.

Use `Set.eq_univ_of_forall fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ σ '' Reg`. Rewrite `hx` using `[hσReg, Set.mem_iUnion]`. Take `⟨j, hj⟩` from `hx`. Conclude with `Set.mem_iUnion.2 ⟨j + 1, hj⟩`.

Conclude with `Set.mem_iUnion.2 ⟨0, hx⟩`. Establish `hsum` using `hCA n d W A f φ E hW hdim hA hf.continuous hfc hφ hEm hEd`. Rewrite `hsum` using `[hEU, Set.indicator_univ]`. Establish `h0 : chartInt W A ((E 0).indicator f) φ = 0` using `hOR n d W A σ r N hσ hcov f φ hfN`. Establish `hi : ∀ j, chartInt W A ((E (j + 1)).indicator f) φ = ∫ w in P j, F w` using `fun j => hPI n d W A σ r r' N hσ hinj hN hrr hprop hcov f φ (P j) hφ (hPm j) (hPB j) (fun w hw => ⟨(hPsub j hw).2.1, (hPsub j hw).2.2⟩) (hPinj j)`.

Establish `hL : HasSum (fun j => ∫ w in P j, F w) (chartInt W A f φ)`. Establish `h1` using `(hasSum_nat_add_iff' 1).2 hsum`. Rewrite `h1` using `[Finset.sum_range_one, h0, sub_zero]`. Establish `h2 : (fun j => chartInt W A ((E (j + 1)).indicator f) φ) = fun j => ∫ w in P j, F w`. Use function extensionality and compare the values at `hi`.

Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Establish `hint : IntegrableOn F (Metric.ball 0 r)` using `hDI n d W σ r r' N hσ hrr hprop f φ hf.continuous hfN hφ`. Establish `hR : HasSum (fun j => ∫ w in P j, F w) (∫ w in Reg, F w)`. Establish `h1` using `hasSum_integral_iUnion hPm hPd (by rw [hPReg]; exact hint.mono_set hRegB)`. Rewrite `h1` using `[hPReg]`. Then use the resulting hypothesis.

Establish `hnull` using `hCN n d W A σ r N hW hdim hA hσ hinj hN fun w hw hwN => (hprop w hw hwN).1`. Establish `hB : ∫ w in Metric.ball 0 r, F w = ∫ w in Reg, F w`. Use `setIntegral_eq_of_subset_of_ae_sdiff_eq_zero Metric.isOpen_ball.measurableSet.nullMeasurableSet hRegB ?_` and prove the remaining obligations. Establish `hae : ∀ᵐ w ∂(volume : Measure (Fin d → ℂ)), w ∉ {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0}` using `measure_eq_zero_iff_ae_notMem.1 hnull`. Use `filter_upwards [hae] with w hw hwd`.

Take `⟨hwB, hwR⟩` from `hwd`. Distinguish the cases in `hwN : σ w ∈ N`. It suffices to derive a contradiction. Distinguish the cases in `hdet : LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0`. Conclude with `hw ⟨hwB, hwN, hdet⟩`.

Conclude with `hwR ⟨hwB, hwN, hdet⟩`. Use `show f (σ w) * _ = 0`. Rewrite using `[hf0 _ hwN, zero_mul]`. Rewrite using `[hB]`. Conclude with `hL.unique hR`.
-/
theorem ParamChartInt.proof (hCA : ChartIntCountAdd.Statement) (hPI : ParamPieceInt.Statement)
    (hCN : ParamCritNull.Statement) (hOR : ParamOffRegularZero.Statement)
    (hRP : RegularInjectivePieces.Statement) (hDI : ParamDensIntegrable.Statement) :
    ParamChartInt.Statement := by
  intro n d W A σ r r' N hW hdim hA hσ hinj hN hrr hprop hcov f φ hf hfc hfN hφ
  classical
  set F : (Fin d → ℂ) → ℝ := fun w => f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w with hF
  have hf0 : ∀ x, x ∉ N → f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hfN h)
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  set Ω : Set (Fin d → ℂ) := Metric.ball 0 r ∩ σ ⁻¹' N with hΩ
  have hΩo : IsOpen Ω := hσ.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hN
  have hmv : Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) := by
    have h := (Matrix.mulVecLin A).toContinuousLinearMap.differentiable
    convert h using 1
    funext x
    simp
  have hgd : DifferentiableOn ℂ g Ω := hmv.comp_differentiableOn (hσ.mono Set.inter_subset_left)
  set Reg : Set (Fin d → ℂ) := {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
      LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} with hReg
  obtain ⟨P, hPm, hPd, hPU, hPinj⟩ := hRP d Ω g hΩo hgd
  have hPReg : ⋃ i, P i = Reg := by
    rw [hPU]; ext w
    simp only [hΩ, Reg, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, and_assoc]
  have hPsub : ∀ i, P i ⊆ Reg := fun i => hPReg ▸ Set.subset_iUnion P i
  have hRegB : Reg ⊆ Metric.ball 0 r := fun w hw => hw.1
  have hPB : ∀ i, P i ⊆ Metric.ball 0 r := fun i => (hPsub i).trans hRegB
  have hσP : ∀ i, MeasurableSet (σ '' P i) := fun i =>
    (hPm i).image_of_continuousOn_injOn (hσ.continuousOn.mono (hPB i)) (hinj.mono (hPB i))
  have hσReg : σ '' Reg = ⋃ i, σ '' P i := by rw [← hPReg, Set.image_iUnion]

  let E : ℕ → Set (Fin n → ℂ) := fun i => Nat.casesOn i (σ '' Reg)ᶜ fun j => σ '' P j
  have hEm : ∀ i, MeasurableSet (E i) := by
    intro i
    cases i with
    | zero => show MeasurableSet (σ '' Reg)ᶜ; rw [hσReg]; exact (MeasurableSet.iUnion hσP).compl
    | succ j => exact hσP j
  have hdisjP : ∀ i j, i ≠ j → Disjoint (σ '' P i) (σ '' P j) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hba := hinj (hPB j hb) (hPB i ha) hab
    subst hba
    exact Set.disjoint_left.1 (hPd hij) ha hb
  have hEd : Pairwise (Function.onFun Disjoint E) := by
    intro i j hij
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ j => exact Set.disjoint_compl_left_iff_subset.2 (Set.image_mono (hPsub j))
    | succ i =>
      cases j with
      | zero => exact Set.disjoint_compl_right_iff_subset.2 (Set.image_mono (hPsub i))
      | succ j => exact hdisjP i j fun h => hij (by rw [h])
  have hEU : ⋃ i, E i = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ σ '' Reg
    · rw [hσReg, Set.mem_iUnion] at hx
      obtain ⟨j, hj⟩ := hx
      exact Set.mem_iUnion.2 ⟨j + 1, hj⟩
    · exact Set.mem_iUnion.2 ⟨0, hx⟩

  have hsum := hCA n d W A f φ E hW hdim hA hf.continuous hfc hφ hEm hEd
  rw [hEU, Set.indicator_univ] at hsum
  have h0 : chartInt W A ((E 0).indicator f) φ = 0 := hOR n d W A σ r N hσ hcov f φ hfN
  have hi : ∀ j, chartInt W A ((E (j + 1)).indicator f) φ = ∫ w in P j, F w := fun j =>
    hPI n d W A σ r r' N hσ hinj hN hrr hprop hcov f φ (P j) hφ (hPm j) (hPB j)
      (fun w hw => ⟨(hPsub j hw).2.1, (hPsub j hw).2.2⟩) (hPinj j)
  have hL : HasSum (fun j => ∫ w in P j, F w) (chartInt W A f φ) := by
    have h1 := (hasSum_nat_add_iff' 1).2 hsum
    rw [Finset.sum_range_one, h0, sub_zero] at h1
    have h2 : (fun j => chartInt W A ((E (j + 1)).indicator f) φ) = fun j => ∫ w in P j, F w :=
      funext hi
    rwa [h2] at h1

  have hint : IntegrableOn F (Metric.ball 0 r) :=
    hDI n d W σ r r' N hσ hrr hprop f φ hf.continuous hfN hφ
  have hR : HasSum (fun j => ∫ w in P j, F w) (∫ w in Reg, F w) := by
    have h1 := hasSum_integral_iUnion hPm hPd (by rw [hPReg]; exact hint.mono_set hRegB)
    rwa [hPReg] at h1
  have hnull := hCN n d W A σ r N hW hdim hA hσ hinj hN fun w hw hwN => (hprop w hw hwN).1
  have hB : ∫ w in Metric.ball 0 r, F w = ∫ w in Reg, F w := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      Metric.isOpen_ball.measurableSet.nullMeasurableSet hRegB ?_
    have hae : ∀ᵐ w ∂(volume : Measure (Fin d → ℂ)), w ∉ {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧
        σ w ∈ N ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} :=
      measure_eq_zero_iff_ae_notMem.1 hnull
    filter_upwards [hae] with w hw hwd
    obtain ⟨hwB, hwR⟩ := hwd
    by_cases hwN : σ w ∈ N
    · exfalso
      by_cases hdet : LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0
      · exact hw ⟨hwB, hwN, hdet⟩
      · exact hwR ⟨hwB, hwN, hdet⟩
    · show f (σ w) * _ = 0
      rw [hf0 _ hwN, zero_mul]
  rw [hB]
  exact hL.unique hR

end

end GroundTheory.Heights₂.Heights
