import ReciprocityTheory.SemistableReduction.SphereTorusB
import ReciprocityTheory.SemistableReduction.SphereTorusC

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory

/- English proof (translation)
Introduce `B n a f hn hf hhom`. Use `haveI : IsProbabilityMeasure (sphereProb n) := isProbabilityMeasure_sphereProb hn`. Use `haveI : IsProbabilityMeasure (blockSphereProb B n) := by`. Unfold `blockSphereProb`. Use `infer_instance`.

Use `haveI : IsProbabilityMeasure ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by simp⟩`. Use `haveI : IsProbabilityMeasure (torusProb (Fin B × Fin n)) := by`. Unfold `torusProb`. Use `infer_instance`. Establish `hh : Integrable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖) (blockSphereProb B n)` using `hInt B n a f hf hhom`.

Establish `hslice : ∀ θ : Fin B × Fin n → ℝ, Integrable (fun z => Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖) (blockSphereProb B n) ∧ ∫ z, Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖ ∂(blockSphereProb B n) = blockSphereMean B n f …`. Introduce `θ`. Establish `hmp` using `measurePreserving_blockRot (B := B) (n := n) θ`. Establish `e : ∀ z, (fun p => blockPoint z p * torusPoint θ p) = blockPoint (blockRot θ z)`. Introduce `z`.

Rewrite using `[blockPoint_blockRot]`. Simplify using `only [e]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Integrable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖) (Measure.map (blockRot θ) (blockSphereProb B n))`. Rewrite using `[hmp.map_eq]`.

Conclude with `hh`. Conclude with `h1.comp_measurable hmp.measurable`. Establish `hA : AEStronglyMeasurable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖) (Measure.map (blockRot θ) (blockSphereProb B n))`. Rewrite using `[hmp.map_eq]`. Conclude with `hh.aestronglyMeasurable`.

Establish `h2` using `integral_map hmp.measurable.aemeasurable hA`. Rewrite `h2` using `[hmp.map_eq]`. Conclude with `h2.symm`. Establish `hA : AEStronglyMeasurable (fun z => ‖Real.log ‖MvPolynomial.eval (blockPoint z) f‖‖) (Measure.map (blockRot θ) (blockSphereProb B n))`. Rewrite using `[hmp.map_eq]`.

Conclude with `hh.norm.aestronglyMeasurable`. Establish `h2` using `integral_map hmp.measurable.aemeasurable hA`. Rewrite `h2` using `[hmp.map_eq]`. Conclude with `h2.symm`. Establish `hcont : Continuous (fun q : BlockSphere B n × (Fin B × Fin n → ℝ) => MvPolynomial.eval (fun p => blockPoint q.1 p * torusPoint q.2 p) f)`.

Use `(MvPolynomial.continuous_eval f).comp (continuous_pi fun p => ?_)` and prove the remaining obligations. Use `Continuous.mul ?_ ?_` and prove the remaining obligations. Unfold `blockPoint spherePoint fun_prop`. Unfold `torusPoint fun_prop`. Establish `hgm : AEStronglyMeasurable (fun q : BlockSphere B n × (Fin B × Fin n → ℝ) => Real.log ‖MvPolynomial.eval (fun p => blockPoint q.1 p * torusPoint q.2 p) f‖) ((blockSphereProb B n).prod (torusProb (Fin B × Fin n)))` using `(Real.measurable_log.comp hcont.norm.measurable).aestronglyMeasurable`.

Establish `hgi : Integrable (fun q : BlockSphere B n × (Fin B × Fin n → ℝ) => Real.log ‖MvPolynomial.eval (fun p => blockPoint q.1 p * torusPoint q.2 p) f‖) ((blockSphereProb B n).prod (torusProb (Fin B × Fin n)))`. Rewrite using `[integrable_prod_iff' hgm]`. Use `⟨Filter.Eventually.of_forall fun θ => (hslice θ).1, ?_⟩` and prove the remaining obligations. Simplify using `only [fun θ => (hslice θ).2.2]`. Conclude with `integrable_const _`.

Establish `hae : ∀ᵐ z ∂(blockSphereProb B n), ∀ p, blockPoint z p ≠ 0`. Rewrite using `[ae_iff]`. Simplify `blockSphereProb_coord_zero (B := B) (n := n)` using `[not_forall]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [fun θ => (hslice θ).2.1]`.

Simplify using the standard rewrite rules. Use `_ = ∫ z, ∫ θ, Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖ ∂(torusProb (Fin B × Fin n)) ∂(blockSphereProb B n) := (integral_integral_swap hgi).symm`. Use `_ = ∫ z, scaledTorusMean (blockPoint z) f ∂(blockSphereProb B n) := rfl`. Use `_ ≤ ∫ _z, torusMean f ∂(blockSphereProb B n) := by`. Use `integral_mono_ae hgi.integral_prod_left (integrable_const _) ?_` and prove the remaining obligations.

Use `filter_upwards [hae] with z hz`. Conclude with `scaledTorusMean_le_torusMean hBasic f hf (blockPoint z) hz (norm_blockPoint_le z)`. Use `_ = torusMean f := by simp`.
-/
theorem sphereTorus_holds (hInt : SphereLogIntegrableStatement) (hBasic : TorusMeanBasicStatement) :
    SphereLeTorusStatement := by
  intro B n a f hn hf hhom
  haveI : IsProbabilityMeasure (sphereProb n) := isProbabilityMeasure_sphereProb hn
  haveI : IsProbabilityMeasure (blockSphereProb B n) := by
    unfold blockSphereProb; infer_instance
  haveI : IsProbabilityMeasure ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by simp⟩
  haveI : IsProbabilityMeasure (torusProb (Fin B × Fin n)) := by
    unfold torusProb; infer_instance

  have hh : Integrable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖)
      (blockSphereProb B n) := hInt B n a f hf hhom

  have hslice : ∀ θ : Fin B × Fin n → ℝ,
      Integrable (fun z => Real.log ‖MvPolynomial.eval
        (fun p => blockPoint z p * torusPoint θ p) f‖) (blockSphereProb B n) ∧
      ∫ z, Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖
        ∂(blockSphereProb B n) = blockSphereMean B n f ∧
      ∫ z, ‖Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖‖
        ∂(blockSphereProb B n) =
        ∫ z, ‖Real.log ‖MvPolynomial.eval (blockPoint z) f‖‖ ∂(blockSphereProb B n) := by
    intro θ
    have hmp := measurePreserving_blockRot (B := B) (n := n) θ
    have e : ∀ z, (fun p => blockPoint z p * torusPoint θ p) = blockPoint (blockRot θ z) := by
      intro z; rw [blockPoint_blockRot]
    simp only [e]
    refine ⟨?_, ?_, ?_⟩
    · have h1 : Integrable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖)
          (Measure.map (blockRot θ) (blockSphereProb B n)) := by
        rw [hmp.map_eq]; exact hh
      exact h1.comp_measurable hmp.measurable
    · have hA : AEStronglyMeasurable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖)
          (Measure.map (blockRot θ) (blockSphereProb B n)) := by
        rw [hmp.map_eq]; exact hh.aestronglyMeasurable
      have h2 := integral_map hmp.measurable.aemeasurable hA
      rw [hmp.map_eq] at h2
      exact h2.symm
    · have hA : AEStronglyMeasurable (fun z => ‖Real.log ‖MvPolynomial.eval (blockPoint z) f‖‖)
          (Measure.map (blockRot θ) (blockSphereProb B n)) := by
        rw [hmp.map_eq]; exact hh.norm.aestronglyMeasurable
      have h2 := integral_map hmp.measurable.aemeasurable hA
      rw [hmp.map_eq] at h2
      exact h2.symm

  have hcont : Continuous (fun q : BlockSphere B n × (Fin B × Fin n → ℝ) =>
      MvPolynomial.eval (fun p => blockPoint q.1 p * torusPoint q.2 p) f) := by
    refine (MvPolynomial.continuous_eval f).comp (continuous_pi fun p => ?_)
    refine Continuous.mul ?_ ?_
    · unfold blockPoint spherePoint
      fun_prop
    · unfold torusPoint
      fun_prop
  have hgm : AEStronglyMeasurable (fun q : BlockSphere B n × (Fin B × Fin n → ℝ) =>
      Real.log ‖MvPolynomial.eval (fun p => blockPoint q.1 p * torusPoint q.2 p) f‖)
      ((blockSphereProb B n).prod (torusProb (Fin B × Fin n))) :=
    (Real.measurable_log.comp hcont.norm.measurable).aestronglyMeasurable
  have hgi : Integrable (fun q : BlockSphere B n × (Fin B × Fin n → ℝ) =>
      Real.log ‖MvPolynomial.eval (fun p => blockPoint q.1 p * torusPoint q.2 p) f‖)
      ((blockSphereProb B n).prod (torusProb (Fin B × Fin n))) := by
    rw [integrable_prod_iff' hgm]
    refine ⟨Filter.Eventually.of_forall fun θ => (hslice θ).1, ?_⟩
    simp only [fun θ => (hslice θ).2.2]
    exact integrable_const _

  have hae : ∀ᵐ z ∂(blockSphereProb B n), ∀ p, blockPoint z p ≠ 0 := by
    rw [ae_iff]
    simpa [not_forall] using blockSphereProb_coord_zero (B := B) (n := n)
  calc blockSphereMean B n f
      = ∫ θ, ∫ z, Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖
          ∂(blockSphereProb B n) ∂(torusProb (Fin B × Fin n)) := by
        simp only [fun θ => (hslice θ).2.1]
        simp
    _ = ∫ z, ∫ θ, Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖
          ∂(torusProb (Fin B × Fin n)) ∂(blockSphereProb B n) :=
        (integral_integral_swap hgi).symm
    _ = ∫ z, scaledTorusMean (blockPoint z) f ∂(blockSphereProb B n) := rfl
    _ ≤ ∫ _z, torusMean f ∂(blockSphereProb B n) := by
        refine integral_mono_ae hgi.integral_prod_left (integrable_const _) ?_
        filter_upwards [hae] with z hz
        exact scaledTorusMean_le_torusMean hBasic f hf (blockPoint z) hz (norm_blockPoint_le z)
    _ = torusMean f := by simp

end ReciprocityTheory.MultiplicativeHeights
