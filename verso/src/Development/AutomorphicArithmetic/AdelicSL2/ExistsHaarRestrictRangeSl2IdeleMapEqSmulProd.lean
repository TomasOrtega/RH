import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.MeasurableSetUS
import Development.AutomorphicArithmetic.AdelicSL2.IsOpenEmbeddingProjection
import Development.AutomorphicArithmetic.AdelicSL2.ExistsHaarRestrictRangeEqSmulMapOfInvariant
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.CdMeas
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal

/- English proof (translation)
Introduce `M U μ _`. Use `haveI := M.haar`. Use `haveI : SecondCountableTopology (G1 ℚ × US) := UpperTheory.isOpenEmbedding_projection.isEmbedding.secondCountableTopology`. Use `haveI : SecondCountableTopology (G1 ℚ) := inferInstance`. Use `haveI : BorelSpace (G1 ℚ × US) := inferInstance`.

Use `haveI : IsFiniteMeasureOnCompacts (M.μ.prod (us U)) := inferInstance`. Use `UpperTheory.exists_haar_restrict_range_eq_smul_map_of_invariant GG (G1 ℚ × US) μ pm (M.μ.prod (us U)) UpperTheory.isOpenEmbedding_projection ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[range_pm]`. Express the relevant statement in the definitionally equal form `GroundTheory.Automorphic.AdelicGLn.det ℚ 2 1 ∈ US`. Rewrite using `[map_one]`.

Conclude with `US.one_mem`. Introduce and unpack `_ ⟨p, rfl⟩ _ ⟨q, rfl⟩`. Conclude with `⟨_, (pm_mul p q).symm⟩`. Rewrite using `[range_pm]`. Introduce `a ha`.

Express the relevant statement in the definitionally equal form `GroundTheory.Automorphic.AdelicGLn.det ℚ 2 ((a : GL (Fin 2) (A ℚ))⁻¹) ∈ US`. Rewrite using `[map_inv]`. Conclude with `US.inv_mem ha`. Introduce `h0`. Establish `h1` using `congrArg (fun m : Measure (G1 ℚ × US) => m (Set.univ ×ˢ Set.univ)) h0`.

Simplify using `only [Measure.prod_prod, measure_univ, mul_one, Measure.coe_zero, Pi.zero_apply] at h1`. Conclude with `(isOpen_univ.measure_ne_zero M.μ Set.univ_nonempty) h1`. Introduce `x`. Use `⟨Prod.map ((fun g => x.1 * g) ∘ cD (x.2 : (A ℚ)ˣ)) (fun t => x.2 * t), ?_, fun y => pm_mul x y⟩` and prove the remaining obligations. Conclude with `((measurePreserving_mul_left M.μ x.1).comp (UpperTheory.ConvolutionTheory.R2.M.cdMeas ℚ M _)).prod (us_mul U x.2)`.
-/
theorem UpperTheory.exists_haar_restrict_range_sl2IdeleMap_eq_smul_prod :
    ∀ (M : Meas ℚ) (U : UMeas) (μ : Measure GG) [μ.IsHaarMeasure], ∃ c : ℝ≥0, μ.restrict (Set.range pm) = c • (M.μ.prod (us U)).map pm := by
  intro M U μ _
  haveI := M.haar
  haveI : SecondCountableTopology (G1 ℚ × US) := UpperTheory.isOpenEmbedding_projection.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (G1 ℚ) := inferInstance
  haveI : BorelSpace (G1 ℚ × US) := inferInstance
  haveI : IsFiniteMeasureOnCompacts (M.μ.prod (us U)) := inferInstance
  refine UpperTheory.exists_haar_restrict_range_eq_smul_map_of_invariant GG (G1 ℚ × US) μ pm (M.μ.prod (us U)) UpperTheory.isOpenEmbedding_projection ?_ ?_ ?_ ?_ ?_
  · rw [range_pm]
    change GroundTheory.Automorphic.AdelicGLn.det ℚ 2 1 ∈ US
    rw [map_one]
    exact US.one_mem
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact ⟨_, (pm_mul p q).symm⟩
  · rw [range_pm]
    intro a ha
    change GroundTheory.Automorphic.AdelicGLn.det ℚ 2 ((a : GL (Fin 2) (A ℚ))⁻¹) ∈ US
    rw [map_inv]
    exact US.inv_mem ha
  · intro h0
    have h1 := congrArg (fun m : Measure (G1 ℚ × US) => m (Set.univ ×ˢ Set.univ)) h0
    simp only [Measure.prod_prod, measure_univ, mul_one, Measure.coe_zero, Pi.zero_apply] at h1
    exact (isOpen_univ.measure_ne_zero M.μ Set.univ_nonempty) h1
  · intro x
    refine ⟨Prod.map ((fun g => x.1 * g) ∘ cD (x.2 : (A ℚ)ˣ)) (fun t => x.2 * t), ?_, fun y => pm_mul x y⟩
    exact ((measurePreserving_mul_left M.μ x.1).comp (UpperTheory.ConvolutionTheory.R2.M.cdMeas ℚ M _)).prod (us_mul U x.2)
