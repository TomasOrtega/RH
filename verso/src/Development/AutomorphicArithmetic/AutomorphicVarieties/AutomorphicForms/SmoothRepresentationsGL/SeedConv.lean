import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Establish `hc : ContinuousAt (fun x => (F x / F x₀).re) x₀` using `Complex.continuous_re.continuousAt.comp ((hF.continuousAt hU).div_const _)`. Establish `hp : ∀ᶠ x in 𝓝 x₀, 0 < (F x / F x₀).re` using `hc.eventually (lt_mem_nhds (by simp [div_self h0]))`. Take `⟨r, hr, hb⟩` from `Metric.nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (interior_mem_nhds.2 hU) hp)`. Set `b : ContDiffBump x₀` to `⟨r / 2, r, half_pos hr, half_lt_self hr⟩`. Establish `hs : tsupport b = Metric.closedBall x₀ r` using `b.tsupport_eq`.

Establish `hs' : Function.support b = Metric.ball x₀ r` using `b.support_eq`. Establish `hG : Continuous fun x => b x • (F x / F x₀)`. Use `continuous_of_tsupport fun x hx => ?_` and prove the remaining obligations. Establish `hx' : x ∈ Metric.closedBall x₀ r` using `hs ▸ tsupport_smul_subset_left _ _ hx`. Conclude with `b.continuous.continuousAt.smul ((hF.continuousAt (mem_interior_iff_mem_nhds.1 (hb hx').1)).div_const _)`.

Establish `hK : HasCompactSupport fun x => b x • (F x / F x₀)` using `b.hasCompactSupport.smul_right`. Establish `hI : Integrable (fun x => b x • (F x / F x₀)) μ` using `hG.integrable_of_hasCompactSupport hK`. Establish `hpos : 0 < ∫ x, (b x • (F x / F x₀)).re ∂μ`. Use `(Complex.continuous_re.comp hG).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x₀) (hK.comp_left (g := Complex.re) rfl) (fun x => ?_) ?_` and prove the remaining obligations. Distinguish the cases in `hx : b x = 0`.

Simplify using `[hx]`. Establish `hx' : x ∈ Metric.closedBall x₀ r` using `Metric.ball_subset_closedBall (hs' ▸ hx)`. Establish `h1 : 0 < (F x / F x₀).re` using `(hb hx').2`. Simplify using `using mul_nonneg b.nonneg h1.le`. Establish `h1 : b x₀ = 1` using `b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)`.

Simplify using `[h1, div_self h0]`. Establish `hne : ∫ x, b x • (F x / F x₀) ∂μ ≠ 0`. Introduce `h`. Establish `h2` using `integral_re hI`. Rewrite `h2` using `[h]`.

Simplify using `only [RCLike.re_to_complex, Complex.zero_re] at h2`. Conclude with `hpos.ne' h2`. Use `set c := ∫ x, b x • (F x / F x₀) ∂μ with hc'`. Establish `hd : ContDiff ℝ ∞ fun x => b x • ((F x₀)⁻¹ * c⁻¹)` using `b.contDiff.smul contDiff_const`. Establish `hk : HasCompactSupport fun x => b x • ((F x₀)⁻¹ * c⁻¹)` using `b.hasCompactSupport.smul_right`.

Use `⟨hk.toSchwartzMap hd, ?_⟩` and prove the remaining obligations. Establish `e : ∀ x, F x * (hk.toSchwartzMap hd) x = (b x • (F x / F x₀)) * c⁻¹` using `fun x => by`. Express the relevant statement in the definitionally equal form `F x * (b x • ((F x₀)⁻¹ * c⁻¹)) = _`. Simplify using `only [Complex.real_smul, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [e]`. Rewrite using `[integral_mul_const, ← hc', mul_inv_cancel₀ hne]`.
-/
private theorem exists_schwartz_integral_eq_one {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (F : X → ℂ) (U : Set X) (x₀ : X)
    (hU : U ∈ 𝓝 x₀) (hF : ContinuousOn F U) (h0 : F x₀ ≠ 0) : ∃ α : 𝓢(X, ℂ), ∫ x, F x * α x ∂μ = 1 := by
  have hc : ContinuousAt (fun x => (F x / F x₀).re) x₀ :=
    Complex.continuous_re.continuousAt.comp ((hF.continuousAt hU).div_const _)
  have hp : ∀ᶠ x in 𝓝 x₀, 0 < (F x / F x₀).re :=
    hc.eventually (lt_mem_nhds (by simp [div_self h0]))
  obtain ⟨r, hr, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (interior_mem_nhds.2 hU) hp)
  let b : ContDiffBump x₀ := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hs : tsupport b = Metric.closedBall x₀ r := b.tsupport_eq
  have hs' : Function.support b = Metric.ball x₀ r := b.support_eq
  have hG : Continuous fun x => b x • (F x / F x₀) := by
    refine continuous_of_tsupport fun x hx => ?_
    have hx' : x ∈ Metric.closedBall x₀ r := hs ▸ tsupport_smul_subset_left _ _ hx
    exact b.continuous.continuousAt.smul ((hF.continuousAt (mem_interior_iff_mem_nhds.1 (hb hx').1)).div_const _)
  have hK : HasCompactSupport fun x => b x • (F x / F x₀) := b.hasCompactSupport.smul_right
  have hI : Integrable (fun x => b x • (F x / F x₀)) μ := hG.integrable_of_hasCompactSupport hK
  have hpos : 0 < ∫ x, (b x • (F x / F x₀)).re ∂μ := by
    refine (Complex.continuous_re.comp hG).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x₀)
      (hK.comp_left (g := Complex.re) rfl) (fun x => ?_) ?_
    · by_cases hx : b x = 0
      · simp [hx]
      · have hx' : x ∈ Metric.closedBall x₀ r := Metric.ball_subset_closedBall (hs' ▸ hx)
        have h1 : 0 < (F x / F x₀).re := (hb hx').2
        simpa using mul_nonneg b.nonneg h1.le
    · have h1 : b x₀ = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
      simp [h1, div_self h0]
  have hne : ∫ x, b x • (F x / F x₀) ∂μ ≠ 0 := by
    intro h
    have h2 := integral_re hI
    rw [h] at h2
    simp only [RCLike.re_to_complex, Complex.zero_re] at h2
    exact hpos.ne' h2
  set c := ∫ x, b x • (F x / F x₀) ∂μ with hc'
  have hd : ContDiff ℝ ∞ fun x => b x • ((F x₀)⁻¹ * c⁻¹) := b.contDiff.smul contDiff_const
  have hk : HasCompactSupport fun x => b x • ((F x₀)⁻¹ * c⁻¹) := b.hasCompactSupport.smul_right
  refine ⟨hk.toSchwartzMap hd, ?_⟩
  have e : ∀ x, F x * (hk.toSchwartzMap hd) x = (b x • (F x / F x₀)) * c⁻¹ := fun x => by
    change F x * (b x • ((F x₀)⁻¹ * c⁻¹)) = _
    simp only [Complex.real_smul, div_eq_mul_inv]
    ring
  simp only [e]
  rw [integral_mul_const, ← hc', mul_inv_cancel₀ hne]

/- English proof (translation)
Introduce `h E _ _ _ n W hW y hy`. Use `haveI i1 : (volume : Measure (Rinf E)).IsAddHaarMeasure := inferInstance`. Use `haveI i2 : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Use `haveI i3 : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Use `exists_schwartz_integral_eq_one volume (chart W 1) (invSet E n) (toL y.val) ?_ ?_ ?_` and prove the remaining obligations.

Conclude with `TR.isOpen_invSet.mem_nhds (TR.val_mem_invSet y)`. Conclude with `(h E n W hW).1.comp (f := fun x => ((1 : GA E n), x)) (by fun_prop) fun x hx => ⟨trivial, hx⟩`. Rewrite using `[TR.chart_val, one_mul]`. Conclude with `hy`.
-/
theorem UpperTheory.V.Af.Smo.seedConv :
    UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.SeedConv := by
  intro h E _ _ _ n W hW y hy
  haveI i1 : (volume : Measure (Rinf E)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  refine exists_schwartz_integral_eq_one volume (chart W 1) (invSet E n) (toL y.val) ?_ ?_ ?_
  · exact TR.isOpen_invSet.mem_nhds (TR.val_mem_invSet y)
  · exact (h E n W hW).1.comp (f := fun x => ((1 : GA E n), x)) (by fun_prop) fun x hx => ⟨trivial, hx⟩
  · rw [TR.chart_val, one_mul]
    exact hy
