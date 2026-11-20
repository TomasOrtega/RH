import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfLoc

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology

/- English proof (translation)
Introduce `n m μ hμ f hf x0 hx0`. Set `A` to `fderiv ℝ f x0`. Take `⟨B, hB⟩` from `A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hx0)`. Establish `hRI : Function.RightInverse B A` using `fun y => by`. Simplify using `using congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hB`.

Set `T` to `ContinuousLinearEquiv.equivOfRightInverse A B hRI`. Establish `hT1 : ∀ x, (T x).1 = A x` using `fun x => rfl`. Set `Θ : (Fin n → ℝ) → (Fin n → ℝ)` to `fun x => T.symm (f x, (T x).2)`. Establish `hΘc : ContDiff ℝ 1 Θ` using `T.symm.contDiff.comp (hf.prodMk (contDiff_snd.comp T.contDiff))`. Establish `hfA : ∀ x, A (Θ x) = f x`.

Introduce `x`. Rewrite using `[← hT1]`. Simplify using `[Θ]`. Establish `hd : ∀ x, HasFDerivAt Θ (fderiv ℝ Θ x) x` using `fun x => ((hΘc.differentiable one_ne_zero) x).hasFDerivAt`. Establish `hid : fderiv ℝ Θ x0 = ContinuousLinearMap.id ℝ (Fin n → ℝ)`.

Set `P` to `(ContinuousLinearMap.snd ℝ (Fin m → ℝ) A.ker).comp T.toContinuousLinearMap`. Establish `hP : HasFDerivAt (fun x => (T x).2) P x0` using `P.hasFDerivAt`. Establish `h1 : HasFDerivAt (fun x => (f x, (T x).2)) ((fderiv ℝ f x0).prod P) x0` using `((hf.differentiable one_ne_zero) x0).hasFDerivAt.prodMk hP`. Establish `h2` using `T.symm.toContinuousLinearMap.hasFDerivAt.comp x0 h1`. Rewrite using `[show fderiv ℝ Θ x0 = T.symm.toContinuousLinearMap.comp ((fderiv ℝ f x0).prod P) from h2.fderiv]`.

Use `ext1 y`. Express the relevant statement in the definitionally equal form `T.symm ((fderiv ℝ f x0) y, (T y).2) = y`. Establish `: ((fderiv ℝ f x0) y, (T y).2) = T y` using `Prod.ext (hT1 y).symm rfl`. Rewrite using `[this, ContinuousLinearEquiv.symm_apply_apply]`. Establish `hs : HasStrictFDerivAt Θ ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x0`.

Use `hΘc.contDiffAt.hasStrictFDerivAt (x := x0) one_ne_zero` as an intermediate fact. Rewrite `this` using `[hid]`. Conclude with `this`. Set `PH` to `hs.toOpenPartialHomeomorph Θ`. Establish `hPH : ∀ x, PH x = Θ x` using `fun x => rfl`.

Set `D : (Fin n → ℝ) → ℝ` to `fun x => (fderiv ℝ Θ x).det`. Establish `hDc : Continuous D` using `ContinuousLinearMap.continuous_det.comp (hΘc.continuous_fderiv one_ne_zero)`. Set `N` to `PH.source ∩ {x | D x ≠ 0}`. Establish `hNo : IsOpen N` using `PH.open_source.inter (isOpen_ne_fun hDc continuous_const)`. Establish `hx0N : x0 ∈ N` using `⟨hs.mem_toOpenPartialHomeomorph_source, by show (fderiv ℝ Θ x0).det ≠ 0`.

Rewrite using `[hid, ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]`. Use the proof step `norm_num⟩`. Use `⟨N, hNo, hx0N, A, hx0, fun φ hc hsφ hφN => ?_⟩` and prove the remaining obligations. Set `C` to `PH '' tsupport φ`. Establish `hNsrc : N ⊆ PH.source` using `Set.inter_subset_left`.

Establish `hCc : IsCompact C` using `hsφ.image_of_continuousOn (PH.continuousOn.mono (hφN.trans hNsrc))`. Set `G : (Fin n → ℝ) → ℝ` to `PH.target.indicator fun z => φ (PH.symm z) / |D (PH.symm z)|`. Establish `hGC : ∀ z, z ∉ C → G z = 0`. Introduce `z hz`. Distinguish the cases in `ht : z ∈ PH.target`.

Simplify using `only [G, Set.indicator_of_mem ht]`. Establish `: φ (PH.symm z) = 0`. Assume the negation of the conclusion as `h0`. Conclude with `hz ⟨PH.symm z, subset_tsupport _ h0, PH.right_inv ht⟩`. Rewrite using `[this, zero_div]`.

Simplify using `[G, ht]`. Establish `hNimg : IsOpen (PH '' N)` using `PH.isOpen_image_of_subset_source hNo hNsrc`. Establish `hCN : C ⊆ PH '' N` using `Set.image_mono hφN`. Establish `hGcont : Continuous G`. Rewrite using `[continuous_iff_continuousAt]`.

Introduce `z`. Distinguish the cases in `hz : z ∈ PH '' N`. Take `⟨x, hxN, rfl⟩` from `hz`. Establish `hxs : x ∈ PH.source` using `hNsrc hxN`. Establish `hev : G =ᶠ[𝓝 (PH x)] fun z => φ (PH.symm z) / |D (PH.symm z)|` using `by filter_upwards [PH.open_target.mem_nhds (PH.map_source hxs)] with z hz`.

Simplify using `[G, Set.indicator_of_mem hz]`. Use `ContinuousAt.congr ?_ hev.symm` and prove the remaining obligations. Establish `hsymm : ContinuousAt PH.symm (PH x)` using `PH.continuousAt_symm (PH.map_source hxs)`. Establish `hD0 : D (PH.symm (PH x)) ≠ 0` using `by rw [PH.left_inv hxs]; exact hxN.2`. Conclude with `(hc.continuousAt.comp hsymm).div ((continuous_abs.continuousAt).comp (hDc.continuousAt.comp hsymm)) (abs_ne_zero.2 hD0)`.

Establish `hzC : z ∉ C` using `fun h => hz (hCN h)`. Establish `hev : G =ᶠ[𝓝 z] fun _ => 0` using `by filter_upwards [hCc.isClosed.isOpen_compl.mem_nhds hzC] with w hw`. Conclude with `hGC w hw`. Conclude with `(continuousAt_const).congr hev.symm`. Establish `hGs : HasCompactSupport G` using `HasCompactSupport.intro hCc hGC`.

Use `⟨G, hGcont, hGs, fun S hS => ?_⟩` and prove the remaining obligations. Establish `hSm : MeasurableSet S` using `hS.isClosed.measurableSet`. Establish `hNm : MeasurableSet N` using `hNo.measurableSet`. Establish `hJ` using `integral_image_eq_integral_abs_det_fderiv_smul μ hNm (fun x _ => (hd x).hasFDerivWithinAt) (PH.injOn.mono hNsrc) ((A ⁻¹' S).indicator G)`. Establish `hL : ∫ x in Θ '' N, (A ⁻¹' S).indicator G x ∂μ = ∫ v in A ⁻¹' S, G v ∂μ`.

Rewrite using `[setIntegral_eq_integral_of_forall_compl_eq_zero, integral_indicator (hSm.preimage A.continuous.measurable)]`. Introduce `z hz`. Establish `: G z = 0` using `hGC z fun h => hz (hCN h)`. Simplify using `[Set.indicator, this]`. Establish `hR : ∫ x in N, |(fderiv ℝ Θ x).det| • (A ⁻¹' S).indicator G (Θ x) ∂μ = ∫ v in f ⁻¹' S, φ v ∂μ`.

Establish `e1 : ∀ x ∈ N, |(fderiv ℝ Θ x).det| • (A ⁻¹' S).indicator G (Θ x) = (f ⁻¹' S).indicator φ x`. Introduce `x hxN`. Establish `hxs : x ∈ PH.source` using `hNsrc hxN`. Establish `ht : Θ x ∈ PH.target` using `PH.map_source hxs`. Establish `hl : PH.symm (Θ x) = x` using `PH.left_inv hxs`.

Establish `hD : D x ≠ 0` using `hxN.2`. Distinguish the cases in `hfS : f x ∈ S`. Establish `h1 : Θ x ∈ A ⁻¹' S` using `by simp [hfA, hfS]`. Rewrite using `[Set.indicator_of_mem h1, Set.indicator_of_mem (show x ∈ f ⁻¹' S from hfS)]`. Simplify using `only [G, Set.indicator_of_mem ht, hl, smul_eq_mul]`.

Express the relevant statement in the definitionally equal form `|D x| * (φ x / |D x|) = φ x`. Clear the denominators using the available nonvanishing facts. Establish `h1 : Θ x ∉ A ⁻¹' S` using `by simp [hfA, hfS]`. Rewrite using `[Set.indicator_of_notMem h1, Set.indicator_of_notMem (show x ∉ f ⁻¹' S from hfS), smul_zero]`. Rewrite using `[setIntegral_congr_fun hNm e1, setIntegral_eq_integral_of_forall_compl_eq_zero, integral_indicator (hSm.preimage (hf.continuous.measurable))]`.

Introduce `x hx`. Establish `: φ x = 0` using `image_eq_zero_of_notMem_tsupport fun h => hx (hφN h)`. Simplify using `[Set.indicator, this]`. Rewrite using `[← hR, ← hL, hJ]`.
-/
theorem changeVar_holds : ChangeVar := by
  intro n m μ hμ f hf x0 hx0
  let A := fderiv ℝ f x0
  obtain ⟨B, hB⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hx0)
  have hRI : Function.RightInverse B A := fun y => by
    simpa using congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hB
  let T := ContinuousLinearEquiv.equivOfRightInverse A B hRI
  have hT1 : ∀ x, (T x).1 = A x := fun x => rfl
  let Θ : (Fin n → ℝ) → (Fin n → ℝ) := fun x => T.symm (f x, (T x).2)
  have hΘc : ContDiff ℝ 1 Θ :=
    T.symm.contDiff.comp (hf.prodMk (contDiff_snd.comp T.contDiff))
  have hfA : ∀ x, A (Θ x) = f x := by
    intro x
    rw [← hT1]; simp [Θ]
  have hd : ∀ x, HasFDerivAt Θ (fderiv ℝ Θ x) x :=
    fun x => ((hΘc.differentiable one_ne_zero) x).hasFDerivAt
  have hid : fderiv ℝ Θ x0 = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    let P := (ContinuousLinearMap.snd ℝ (Fin m → ℝ) A.ker).comp T.toContinuousLinearMap
    have hP : HasFDerivAt (fun x => (T x).2) P x0 := P.hasFDerivAt
    have h1 : HasFDerivAt (fun x => (f x, (T x).2)) ((fderiv ℝ f x0).prod P) x0 :=
      ((hf.differentiable one_ne_zero) x0).hasFDerivAt.prodMk hP
    have h2 := T.symm.toContinuousLinearMap.hasFDerivAt.comp x0 h1
    rw [show fderiv ℝ Θ x0 = T.symm.toContinuousLinearMap.comp ((fderiv ℝ f x0).prod P) from
      h2.fderiv]
    ext1 y
    change T.symm ((fderiv ℝ f x0) y, (T y).2) = y
    have : ((fderiv ℝ f x0) y, (T y).2) = T y := Prod.ext (hT1 y).symm rfl
    rw [this, ContinuousLinearEquiv.symm_apply_apply]
  have hs : HasStrictFDerivAt Θ
      ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x0 := by
    have := hΘc.contDiffAt.hasStrictFDerivAt (x := x0) one_ne_zero
    rw [hid] at this
    exact this
  let PH := hs.toOpenPartialHomeomorph Θ
  have hPH : ∀ x, PH x = Θ x := fun x => rfl
  let D : (Fin n → ℝ) → ℝ := fun x => (fderiv ℝ Θ x).det
  have hDc : Continuous D :=
    ContinuousLinearMap.continuous_det.comp (hΘc.continuous_fderiv one_ne_zero)
  let N := PH.source ∩ {x | D x ≠ 0}
  have hNo : IsOpen N := PH.open_source.inter (isOpen_ne_fun hDc continuous_const)
  have hx0N : x0 ∈ N := ⟨hs.mem_toOpenPartialHomeomorph_source, by
    show (fderiv ℝ Θ x0).det ≠ 0
    rw [hid, ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
    norm_num⟩
  refine ⟨N, hNo, hx0N, A, hx0, fun φ hc hsφ hφN => ?_⟩
  let C := PH '' tsupport φ
  have hNsrc : N ⊆ PH.source := Set.inter_subset_left
  have hCc : IsCompact C :=
    hsφ.image_of_continuousOn (PH.continuousOn.mono (hφN.trans hNsrc))
  let G : (Fin n → ℝ) → ℝ := PH.target.indicator fun z => φ (PH.symm z) / |D (PH.symm z)|
  have hGC : ∀ z, z ∉ C → G z = 0 := by
    intro z hz
    by_cases ht : z ∈ PH.target
    · simp only [G, Set.indicator_of_mem ht]
      have : φ (PH.symm z) = 0 := by
        by_contra h0
        exact hz ⟨PH.symm z, subset_tsupport _ h0, PH.right_inv ht⟩
      rw [this, zero_div]
    · simp [G, ht]
  have hNimg : IsOpen (PH '' N) := PH.isOpen_image_of_subset_source hNo hNsrc
  have hCN : C ⊆ PH '' N := Set.image_mono hφN
  have hGcont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ PH '' N
    · obtain ⟨x, hxN, rfl⟩ := hz
      have hxs : x ∈ PH.source := hNsrc hxN
      have hev : G =ᶠ[𝓝 (PH x)] fun z => φ (PH.symm z) / |D (PH.symm z)| := by
        filter_upwards [PH.open_target.mem_nhds (PH.map_source hxs)] with z hz
        simp [G, Set.indicator_of_mem hz]
      refine ContinuousAt.congr ?_ hev.symm
      have hsymm : ContinuousAt PH.symm (PH x) := PH.continuousAt_symm (PH.map_source hxs)
      have hD0 : D (PH.symm (PH x)) ≠ 0 := by rw [PH.left_inv hxs]; exact hxN.2
      exact (hc.continuousAt.comp hsymm).div
        ((continuous_abs.continuousAt).comp (hDc.continuousAt.comp hsymm))
        (abs_ne_zero.2 hD0)
    · have hzC : z ∉ C := fun h => hz (hCN h)
      have hev : G =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [hCc.isClosed.isOpen_compl.mem_nhds hzC] with w hw
        exact hGC w hw
      exact (continuousAt_const).congr hev.symm
  have hGs : HasCompactSupport G := HasCompactSupport.intro hCc hGC
  refine ⟨G, hGcont, hGs, fun S hS => ?_⟩
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hNm : MeasurableSet N := hNo.measurableSet
  have hJ := integral_image_eq_integral_abs_det_fderiv_smul μ hNm
    (fun x _ => (hd x).hasFDerivWithinAt) (PH.injOn.mono hNsrc)
    ((A ⁻¹' S).indicator G)

  have hL : ∫ x in Θ '' N, (A ⁻¹' S).indicator G x ∂μ = ∫ v in A ⁻¹' S, G v ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_indicator
      (hSm.preimage A.continuous.measurable)]
    intro z hz
    have : G z = 0 := hGC z fun h => hz (hCN h)
    simp [Set.indicator, this]

  have hR : ∫ x in N, |(fderiv ℝ Θ x).det| • (A ⁻¹' S).indicator G (Θ x) ∂μ =
      ∫ v in f ⁻¹' S, φ v ∂μ := by
    have e1 : ∀ x ∈ N, |(fderiv ℝ Θ x).det| • (A ⁻¹' S).indicator G (Θ x) =
        (f ⁻¹' S).indicator φ x := by
      intro x hxN
      have hxs : x ∈ PH.source := hNsrc hxN
      have ht : Θ x ∈ PH.target := PH.map_source hxs
      have hl : PH.symm (Θ x) = x := PH.left_inv hxs
      have hD : D x ≠ 0 := hxN.2
      by_cases hfS : f x ∈ S
      · have h1 : Θ x ∈ A ⁻¹' S := by simp [hfA, hfS]
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show x ∈ f ⁻¹' S from hfS)]
        simp only [G, Set.indicator_of_mem ht, hl, smul_eq_mul]
        change |D x| * (φ x / |D x|) = φ x
        field_simp
      · have h1 : Θ x ∉ A ⁻¹' S := by simp [hfA, hfS]
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (show x ∉ f ⁻¹' S from hfS),
          smul_zero]
    rw [setIntegral_congr_fun hNm e1, setIntegral_eq_integral_of_forall_compl_eq_zero,
      integral_indicator (hSm.preimage (hf.continuous.measurable))]
    intro x hx
    have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hφN h)
    simp [Set.indicator, this]
  rw [← hR, ← hL, hJ]

end PI.VolStabSW
