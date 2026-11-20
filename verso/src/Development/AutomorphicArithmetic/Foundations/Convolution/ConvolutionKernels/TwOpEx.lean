import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QmapPres
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

/- English proof (translation)
Introduce `K _ _ n μ _ e hg hp`. Establish `hp' : MeasurePreserving e.symm μ μ` using `hp.symm e.toHomeomorph.toMeasurableEquiv`. Establish `hg' : ∀ g, e.symm g ∈ Gam K n ↔ g ∈ Gam K n` using `fun g => by rw [← hg, e.apply_symm_apply]`. Take `⟨h1, q1⟩` from `qmapPres (Gam K n) μ e hg hp`. Take `⟨h2, q2⟩` from `qmapPres (Gam K n) μ e.symm hg' hp'`.

Set `U : L2 μ →L[ℂ] L2 μ` to `(Lp.compMeasurePreservingₗᵢ ℂ _ q2).toContinuousLinearMap`. Establish `hU : ∀ ψ : L2 μ, (U ψ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ] fun y => (ψ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e.symm (Quotient.out y)))` using `fun ψ => Lp.coeFn_compMeasurePreserving ψ q2`. Use `⟨U, hU, fun φ => ?_⟩` and prove the remaining obligations. Establish `key : ContinuousLinearMap.adjoint U φ = Lp.compMeasurePreserving _ q1 φ`. Use `ext_inner_right ℂ fun ψ => ?_` and prove the remaining obligations.

Rewrite using `[ContinuousLinearMap.adjoint_inner_left, L2.inner_def, L2.inner_def]`. Establish `a1` using `q1.quasiMeasurePreserving.ae_eq_comp (hU ψ)`. Establish `m : AEStronglyMeasurable (fun y => ⟪(φ : RightCosetSpace (Gam K n) → ℂ) y, (U ψ : RightCosetSpace (Gam K n) → ℂ) y⟫_ℂ) (Measure.map (fun y : RightCosetSpace (Gam K n) => mk (Gam K n) (e (Quotient.out y))) (quotientMeasure (Gam K n) μ))`. Rewrite using `[q1.map_eq]`. Conclude with `(Lp.aestronglyMeasurable φ).inner (Lp.aestronglyMeasurable _)`.

Establish `e1` using `integral_map q1.measurable.aemeasurable m`. Rewrite `e1` using `[q1.map_eq]`. Rewrite using `[e1]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [a1, Lp.coeFn_compMeasurePreserving φ q1] with y hy hz`.

Rewrite using `[hz]`. Simplify using `only [Function.comp_apply] at hy ⊢`. Rewrite using `[hy, h2, e.symm_apply_apply]`. Use `congr 2`. Conclude with `Quotient.out_eq y`.

Rewrite using `[key]`. Conclude with `Lp.coeFn_compMeasurePreserving φ q1`.
-/
theorem UpperTheory.ConvolutionTheory.K.twOpEx :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (e : G1 K n ≃ₜ* G1 K n), (∀ g, e g ∈ Gam K n ↔ g ∈ Gam K n) → MeasurePreserving e μ μ →
      ∃ U : L2 μ →L[ℂ] L2 μ,
        (∀ φ : L2 μ, (U φ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
          fun y => (φ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e.symm (Quotient.out y)))) ∧
        ∀ φ : L2 μ, (ContinuousLinearMap.adjoint U φ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
          fun y => (φ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e (Quotient.out y))) := by
  intro K _ _ n μ _ e hg hp
  have hp' : MeasurePreserving e.symm μ μ := hp.symm e.toHomeomorph.toMeasurableEquiv
  have hg' : ∀ g, e.symm g ∈ Gam K n ↔ g ∈ Gam K n := fun g => by rw [← hg, e.apply_symm_apply]
  obtain ⟨h1, q1⟩ := qmapPres (Gam K n) μ e hg hp
  obtain ⟨h2, q2⟩ := qmapPres (Gam K n) μ e.symm hg' hp'
  let U : L2 μ →L[ℂ] L2 μ := (Lp.compMeasurePreservingₗᵢ ℂ _ q2).toContinuousLinearMap
  have hU : ∀ ψ : L2 μ, (U ψ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
      fun y => (ψ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e.symm (Quotient.out y))) :=
    fun ψ => Lp.coeFn_compMeasurePreserving ψ q2
  refine ⟨U, hU, fun φ => ?_⟩
  have key : ContinuousLinearMap.adjoint U φ = Lp.compMeasurePreserving _ q1 φ := by
    refine ext_inner_right ℂ fun ψ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def, L2.inner_def]
    have a1 := q1.quasiMeasurePreserving.ae_eq_comp (hU ψ)
    have m : AEStronglyMeasurable (fun y => ⟪(φ : RightCosetSpace (Gam K n) → ℂ) y, (U ψ : RightCosetSpace (Gam K n) → ℂ) y⟫_ℂ)
        (Measure.map (fun y : RightCosetSpace (Gam K n) => mk (Gam K n) (e (Quotient.out y))) (quotientMeasure (Gam K n) μ)) := by
      rw [q1.map_eq]
      exact (Lp.aestronglyMeasurable φ).inner (Lp.aestronglyMeasurable _)
    have e1 := integral_map q1.measurable.aemeasurable m
    rw [q1.map_eq] at e1
    rw [e1]
    refine integral_congr_ae ?_
    filter_upwards [a1, Lp.coeFn_compMeasurePreserving φ q1] with y hy hz
    rw [hz]
    simp only [Function.comp_apply] at hy ⊢
    rw [hy, h2, e.symm_apply_apply]
    congr 2
    exact Quotient.out_eq y
  rw [key]
  exact Lp.coeFn_compMeasurePreserving φ q1
