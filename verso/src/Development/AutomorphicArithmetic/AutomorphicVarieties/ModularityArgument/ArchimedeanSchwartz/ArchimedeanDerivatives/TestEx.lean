import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ShiftOf
import GroundTheory.AutomorphicForms.GL2.InnerProductParamHolo

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace UpperTheory.V.Z.Inf

/- English proof (translation)
Use `haveI : ProperSpace E := FiniteDimensional.proper ℝ E`. Use `set c : ℂ := starRingEnd ℂ (f x₀) with hc`. Establish `hre : 0 < (c * f x₀).re`. Rewrite using `[hc, mul_comm, Complex.mul_conj, Complex.ofReal_re]`. Conclude with `Complex.normSq_pos.2 h0`.

Establish `hca : ContinuousAt (fun x => (c * f x).re) x₀` using `Complex.continuous_re.continuousAt.comp (continuousAt_const.mul (hf.continuousAt (hU.mem_nhds hx₀)))`. Establish `hW : U ∩ {x | 0 < (c * f x).re} ∈ 𝓝 x₀` using `inter_mem (hU.mem_nhds hx₀) (hca.eventually (lt_mem_nhds hre))`. Take `⟨ε, hε, hball⟩` from `Metric.nhds_basis_closedBall.mem_iff.1 hW`. Set `ψ : ContDiffBump x₀` to `⟨ε / 2, ε, by positivity, by linarith⟩`. Establish `hψz : ∀ x, x ∉ closedBall x₀ ε → ψ x = 0` using `fun x hx => by`.

Assume the negation of the conclusion as `h`. Establish `: x ∈ Function.support ψ` using `h`. Rewrite `this` using `[ψ.support_eq]`. Conclude with `hx (ball_subset_closedBall this)`. Establish `hKc : IsCompact (closedBall x₀ ε)` using `isCompact_closedBall _ _`.

Establish `hKU : closedBall x₀ ε ⊆ U` using `fun x hx => (hball hx).1`. Set `F : ℂ → E → ℂ` to `fun s x => (ψ x : ℂ) * f x * ((A x : ℝ) : ℂ) ^ s`. Establish `hFz : ∀ s x, x ∉ closedBall x₀ ε → F s x = 0` using `fun s x hx => by`. Simplify using `only [F, hψz x hx, Complex.ofReal_zero, zero_mul]`. Establish `hts : ∀ {G : E → ℂ}, (∀ x, x ∉ closedBall x₀ ε → G x = 0) → tsupport G ⊆ closedBall x₀ ε` using `fun h => closure_minimal (fun x hx => by by_contra h'; exact hx (h x h')) isClosed_closedBall`.

Establish `hJ : ContinuousOn (fun p : ℂ × E => F p.1 p.2) (univ ×ˢ U)`. Use `ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_` and prove the remaining obligations. Conclude with `(Complex.continuous_ofReal.comp (ψ.continuous.comp continuous_snd)).continuousOn`. Conclude with `hf.comp continuousOn_snd fun p hp => hp.2`. Conclude with `ContinuousOn.cpow (Complex.continuous_ofReal.comp (hA.comp continuous_snd)).continuousOn continuousOn_fst fun p hp => Complex.ofReal_mem_slitPlane.2 (hA0 _ hp.2)`.

Establish `hFc : ∀ s, Continuous (F s)` using `fun s => by`. Establish `: ContinuousOn (F s) U` using `hJ.comp (f := fun x : E => (s, x)) (by fun_prop) fun x hx => ⟨trivial, hx⟩`. Conclude with `this.continuous_of_tsupport_subset hU ((hts (hFz s)).trans hKU)`. Establish `hFi : ∀ s, Integrable (F s) μ` using `fun s => (hFc s).integrable_of_hasCompactSupport (HasCompactSupport.intro hKc (hFz s))`. Establish `hΦz : ∀ x, x ∉ closedBall x₀ ε → (ψ x : ℂ) = 0` using `fun x hx => by`.

Rewrite using `[hψz x hx, Complex.ofReal_zero]`. Use `⟨fun x => (ψ x : ℂ), ⟨?_, HasCompactSupport.intro hKc hΦz, (hts hΦz).trans hKU⟩, ?_, 0, ?_⟩` and prove the remaining obligations. Conclude with `Complex.ofRealCLM.contDiff.comp ψ.contDiff`. Rewrite using `[← differentiableOn_univ]`. Use `GroundTheory.Automorphic.PseudoEisenstein.differentiableOn_integral_of_bound (F := F) isOpen_univ (fun x => ?_) (fun s _ => (hFc s).aestronglyMeasurable) fun s₀ _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hx : x ∈ closedBall x₀ ε`. Use `Differentiable.differentiableOn ?_` and prove the remaining obligations. Conclude with `(differentiable_id.const_cpow (Or.inl (by exact_mod_cast (hA0 x (hKU hx)).ne'))).const_mul _`. Simplify using `only [hFz _ x hx]`. Conclude with `differentiableOn_const _`.

Take `⟨C, hC⟩` from `((isCompact_closedBall s₀ 1).prod hKc).exists_bound_of_continuousOn (hJ.mono (prod_mono (subset_univ _) hKU))`. Use `⟨1, one_pos, subset_univ _, (closedBall x₀ ε).indicator fun _ => C, ?_, fun s hs x => ?_⟩` and prove the remaining obligations. Rewrite using `[integrable_indicator_iff isClosed_closedBall.measurableSet]`. Conclude with `integrableOn_const hKc.measure_lt_top.ne`. Distinguish the cases in `hx : x ∈ closedBall x₀ ε`.

Rewrite using `[indicator_of_mem hx]`. Conclude with `hC (s, x) ⟨hs, hx⟩`. Rewrite using `[indicator_of_notMem hx, hFz s x hx, norm_zero]`. Introduce `hz`. Express the relevant statement in the definitionally equal form `∫ x, F 0 x ∂μ = 0 at hz`.

Establish `hr : ∀ x, (c * F 0 x).re = ψ x * (c * f x).re` using `fun x => by`. Simplify using `only [F, Complex.cpow_zero, mul_one]`. Rewrite using `[mul_left_comm, Complex.re_ofReal_mul]`. Establish `hrc : Continuous fun x => (c * F 0 x).re` using `Complex.continuous_re.comp (continuous_const.mul (hFc 0))`. Establish `hr0 : 0 ≤ fun x => (c * F 0 x).re` using `fun x => by`.

Express the relevant statement in the definitionally equal form `0 ≤ (c * F 0 x).re`. Distinguish the cases in `hx : x ∈ closedBall x₀ ε`. Rewrite using `[hr]`. Conclude with `mul_nonneg ψ.nonneg (le_of_lt (hball hx).2)`. Rewrite using `[hFz 0 x hx]`.

Simplify using the standard rewrite rules. Establish `hri : Integrable (fun x => (c * F 0 x).re) μ` using `((hFi 0).const_mul c).re`. Establish `hpos : 0 < ∫ x, (c * F 0 x).re ∂μ`. Rewrite using `[integral_pos_iff_support_of_nonneg hr0 hri]`. Use `hrc.isOpen_support.measure_pos μ ⟨x₀, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(c * F 0 x₀).re ≠ 0`. Rewrite using `[hr, ψ.one_of_mem_closedBall (mem_closedBall_self ψ.rIn_pos.le), one_mul]`. Conclude with `hre.ne'`. Establish `h1` using `integral_re ((hFi 0).const_mul c)`. Simplify using `only [RCLike.re_to_complex] at h1`.

Rewrite `hpos` using `[h1, integral_const_mul, hz, mul_zero, Complex.zero_re]`. Conclude with `lt_irrefl _ hpos`.
-/
private theorem testEx_gen {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {U : Set E} (hU : IsOpen U) {f : E → ℂ} (hf : ContinuousOn f U) {A : E → ℝ} (hA : Continuous A)
    (hA0 : ∀ x ∈ U, 0 < A x) {x₀ : E} (hx₀ : x₀ ∈ U) (h0 : f x₀ ≠ 0) :
    ∃ Φ : E → ℂ, (ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ U) ∧
      (Differentiable ℂ fun s : ℂ => ∫ x, Φ x * f x * ((A x : ℝ) : ℂ) ^ s ∂μ) ∧
      ∃ s : ℂ, ∫ x, Φ x * f x * ((A x : ℝ) : ℂ) ^ s ∂μ ≠ 0 := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  set c : ℂ := starRingEnd ℂ (f x₀) with hc
  have hre : 0 < (c * f x₀).re := by
    rw [hc, mul_comm, Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_pos.2 h0
  have hca : ContinuousAt (fun x => (c * f x).re) x₀ :=
    Complex.continuous_re.continuousAt.comp (continuousAt_const.mul (hf.continuousAt (hU.mem_nhds hx₀)))
  have hW : U ∩ {x | 0 < (c * f x).re} ∈ 𝓝 x₀ :=
    inter_mem (hU.mem_nhds hx₀) (hca.eventually (lt_mem_nhds hre))
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hW
  let ψ : ContDiffBump x₀ := ⟨ε / 2, ε, by positivity, by linarith⟩
  have hψz : ∀ x, x ∉ closedBall x₀ ε → ψ x = 0 := fun x hx => by
    by_contra h
    have : x ∈ Function.support ψ := h
    rw [ψ.support_eq] at this
    exact hx (ball_subset_closedBall this)
  have hKc : IsCompact (closedBall x₀ ε) := isCompact_closedBall _ _
  have hKU : closedBall x₀ ε ⊆ U := fun x hx => (hball hx).1
  let F : ℂ → E → ℂ := fun s x => (ψ x : ℂ) * f x * ((A x : ℝ) : ℂ) ^ s
  have hFz : ∀ s x, x ∉ closedBall x₀ ε → F s x = 0 := fun s x hx => by
    simp only [F, hψz x hx, Complex.ofReal_zero, zero_mul]
  have hts : ∀ {G : E → ℂ}, (∀ x, x ∉ closedBall x₀ ε → G x = 0) → tsupport G ⊆ closedBall x₀ ε := fun h =>
    closure_minimal (fun x hx => by by_contra h'; exact hx (h x h')) isClosed_closedBall
  have hJ : ContinuousOn (fun p : ℂ × E => F p.1 p.2) (univ ×ˢ U) := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact (Complex.continuous_ofReal.comp (ψ.continuous.comp continuous_snd)).continuousOn
    · exact hf.comp continuousOn_snd fun p hp => hp.2
    · exact ContinuousOn.cpow (Complex.continuous_ofReal.comp (hA.comp continuous_snd)).continuousOn
        continuousOn_fst fun p hp => Complex.ofReal_mem_slitPlane.2 (hA0 _ hp.2)
  have hFc : ∀ s, Continuous (F s) := fun s => by
    have : ContinuousOn (F s) U :=
      hJ.comp (f := fun x : E => (s, x)) (by fun_prop) fun x hx => ⟨trivial, hx⟩
    exact this.continuous_of_tsupport_subset hU ((hts (hFz s)).trans hKU)
  have hFi : ∀ s, Integrable (F s) μ := fun s =>
    (hFc s).integrable_of_hasCompactSupport (HasCompactSupport.intro hKc (hFz s))
  have hΦz : ∀ x, x ∉ closedBall x₀ ε → (ψ x : ℂ) = 0 := fun x hx => by
    rw [hψz x hx, Complex.ofReal_zero]
  refine ⟨fun x => (ψ x : ℂ), ⟨?_, HasCompactSupport.intro hKc hΦz, (hts hΦz).trans hKU⟩, ?_, 0, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ψ.contDiff
  · rw [← differentiableOn_univ]
    refine GroundTheory.Automorphic.PseudoEisenstein.differentiableOn_integral_of_bound (F := F) isOpen_univ
      (fun x => ?_) (fun s _ => (hFc s).aestronglyMeasurable) fun s₀ _ => ?_
    · by_cases hx : x ∈ closedBall x₀ ε
      · refine Differentiable.differentiableOn ?_
        exact (differentiable_id.const_cpow (Or.inl (by exact_mod_cast (hA0 x (hKU hx)).ne'))).const_mul _
      · simp only [hFz _ x hx]
        exact differentiableOn_const _
    · obtain ⟨C, hC⟩ := ((isCompact_closedBall s₀ 1).prod hKc).exists_bound_of_continuousOn
        (hJ.mono (prod_mono (subset_univ _) hKU))
      refine ⟨1, one_pos, subset_univ _, (closedBall x₀ ε).indicator fun _ => C, ?_, fun s hs x => ?_⟩
      · rw [integrable_indicator_iff isClosed_closedBall.measurableSet]
        exact integrableOn_const hKc.measure_lt_top.ne
      · by_cases hx : x ∈ closedBall x₀ ε
        · rw [indicator_of_mem hx]
          exact hC (s, x) ⟨hs, hx⟩
        · rw [indicator_of_notMem hx, hFz s x hx, norm_zero]
  · intro hz
    change ∫ x, F 0 x ∂μ = 0 at hz
    have hr : ∀ x, (c * F 0 x).re = ψ x * (c * f x).re := fun x => by
      simp only [F, Complex.cpow_zero, mul_one]
      rw [mul_left_comm, Complex.re_ofReal_mul]
    have hrc : Continuous fun x => (c * F 0 x).re :=
      Complex.continuous_re.comp (continuous_const.mul (hFc 0))
    have hr0 : 0 ≤ fun x => (c * F 0 x).re := fun x => by
      change 0 ≤ (c * F 0 x).re
      by_cases hx : x ∈ closedBall x₀ ε
      · rw [hr]
        exact mul_nonneg ψ.nonneg (le_of_lt (hball hx).2)
      · rw [hFz 0 x hx]; simp
    have hri : Integrable (fun x => (c * F 0 x).re) μ := ((hFi 0).const_mul c).re
    have hpos : 0 < ∫ x, (c * F 0 x).re ∂μ := by
      rw [integral_pos_iff_support_of_nonneg hr0 hri]
      refine hrc.isOpen_support.measure_pos μ ⟨x₀, ?_⟩
      change (c * F 0 x₀).re ≠ 0
      rw [hr, ψ.one_of_mem_closedBall (mem_closedBall_self ψ.rIn_pos.le), one_mul]
      exact hre.ne'
    have h1 := integral_re ((hFi 0).const_mul c)
    simp only [RCLike.re_to_complex] at h1
    rw [h1, integral_const_mul, hz, mul_zero, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos

end UpperTheory.V.Z.Inf

/- English proof (translation)
Introduce `K _ _ _ n f hf ⟨x₀, hx₀, h0⟩`. Use `haveI : Measure.IsAddHaarMeasure (volume : Measure (Fin n → GlobalTheory.CuspRep.Cinf K)) := Measure.pi.isAddHaarMeasure _`. Use `haveI : Measure.IsAddHaarMeasure (volume : Measure (GlobalTheory.CuspRep.Lie K n)) := Measure.pi.isAddHaarMeasure _`. Use `UpperTheory.V.Z.Inf.testEx_gen volume GlobalTheory.CuspRep.isOpen_invSet hf (A := UpperTheory.V.Z.Inf.nrm) ?_ ?_ hx₀ h0` and prove the remaining obligations. Unfold `UpperTheory.V.Z.Inf.nrm`.

Use `continuous_finset_prod _ fun w _ => Continuous.pow (Continuous.norm ?_) 2` and prove the remaining obligations. Conclude with `(continuous_apply w).comp (Continuous.matrix_det continuous_id)`. Introduce `x hx`. Establish `hu : IsUnit (Matrix.of x).det` using `(Matrix.isUnit_iff_isUnit_det _).1 hx`. Unfold `UpperTheory.V.Z.Inf.nrm`.

Use `Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ?_) 2` and prove the remaining obligations. Conclude with `(hu.map (Pi.evalMonoidHom _ w)).ne_zero`.
-/
theorem UpperTheory.V.Z.Inf.testEx :
    UpperTheory.V.Z.Inf.TestEx := by
  intro K _ _ _ n f hf ⟨x₀, hx₀, h0⟩
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Fin n → GlobalTheory.CuspRep.Cinf K)) := Measure.pi.isAddHaarMeasure _
  haveI : Measure.IsAddHaarMeasure (volume : Measure (GlobalTheory.CuspRep.Lie K n)) := Measure.pi.isAddHaarMeasure _
  refine UpperTheory.V.Z.Inf.testEx_gen volume GlobalTheory.CuspRep.isOpen_invSet hf (A := UpperTheory.V.Z.Inf.nrm) ?_ ?_ hx₀ h0
  · unfold UpperTheory.V.Z.Inf.nrm
    refine continuous_finset_prod _ fun w _ => Continuous.pow (Continuous.norm ?_) 2
    exact (continuous_apply w).comp (Continuous.matrix_det continuous_id)
  · intro x hx
    have hu : IsUnit (Matrix.of x).det := (Matrix.isUnit_iff_isUnit_det _).1 hx
    unfold UpperTheory.V.Z.Inf.nrm
    refine Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ?_) 2
    exact (hu.map (Pi.evalMonoidHom _ w)).ne_zero
