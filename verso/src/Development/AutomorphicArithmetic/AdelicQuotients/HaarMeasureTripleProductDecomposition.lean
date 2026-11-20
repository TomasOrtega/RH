import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerProd
import Development.WeilBound.ThetaLifts.LatticeBasics.BadFactor

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ A B C hA hB hC j μ hμ μA μB μC hμA hμB hμC f hf`. Use `haveI : LocallyCompactSpace A := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : LocallyCompactSpace C := hC.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : (μB.prod μC).IsHaarMeasure := Measure.prod.instIsHaarMeasure μB μC`.

Use `haveI : SigmaFinite (μB.prod μC) := inferInstance`. Use `haveI : MeasurableMul (B × C) := inferInstance`. Use `haveI hPH : (μA.prod (μB.prod μC)).IsHaarMeasure := Measure.prod.instIsHaarMeasure μA (μB.prod μC)`. Use `set P : Measure (A × B × C) := μA.prod (μB.prod μC) with hP`. Establish `hme : MeasurableEmbedding j` using `j.toHomeomorph.measurableEmbedding`.

Use `haveI hmap : (Measure.map j P).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map P j`. Establish `hk : Measure.map j P = Measure.haarScalarFactor (Measure.map j P) μ • μ` using `Measure.isMulLeftInvariant_eq_smul _ _`. Use `set k : ℝ≥0 := Measure.haarScalarFactor (Measure.map j P) μ with hkdef`. Establish `hfm : Integrable f (Measure.map j P)`. Rewrite using `[hk]; exact hf.smul_measure (by simp)`.

Use `⟨?_, (k : ℝ), ?_⟩` and prove the remaining obligations. Conclude with `(hme.integrable_map_iff).1 hfm`. Establish `h1 : ∫ g, f g ∂(Measure.map j P) = ∫ y, f (j y) ∂P` using `hme.integral_map f`. Rewrite using `[← h1, hk, integral_smul_nnreal_measure]`. Simplify using `[NNReal.smul_def]`.
-/
theorem UpperTheory.haarMeasure_triple_product_decomposition :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B C : Subgroup G), IsClosed (A : Set G) → IsClosed (B : Set G) → IsClosed (C : Set G) → ∀ (j : A × B × C ≃ₜ* G) (μ : Measure G), μ.IsHaarMeasure → ∀ (μA : Measure A) (μB : Measure B) (μC : Measure C), μA.IsHaarMeasure → μB.IsHaarMeasure → μC.IsHaarMeasure → ∀ f : G → ℂ, Integrable f μ → Integrable (fun y => f (j y)) (μA.prod (μB.prod μC)) ∧ ∃ c : ℝ, ∫ y, f (j y) ∂(μA.prod (μB.prod μC)) = c * ∫ g, f g ∂μ := by
  intro G _ _ _ _ _ _ _ _ A B C hA hB hC j μ hμ μA μB μC hμA hμB hμC f hf
  haveI : LocallyCompactSpace A := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace C := hC.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : (μB.prod μC).IsHaarMeasure := Measure.prod.instIsHaarMeasure μB μC
  haveI : SigmaFinite (μB.prod μC) := inferInstance
  haveI : MeasurableMul (B × C) := inferInstance
  haveI hPH : (μA.prod (μB.prod μC)).IsHaarMeasure :=
    Measure.prod.instIsHaarMeasure μA (μB.prod μC)
  set P : Measure (A × B × C) := μA.prod (μB.prod μC) with hP
  have hme : MeasurableEmbedding j := j.toHomeomorph.measurableEmbedding
  haveI hmap : (Measure.map j P).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map P j
  have hk : Measure.map j P = Measure.haarScalarFactor (Measure.map j P) μ • μ :=
    Measure.isMulLeftInvariant_eq_smul _ _
  set k : ℝ≥0 := Measure.haarScalarFactor (Measure.map j P) μ with hkdef
  have hfm : Integrable f (Measure.map j P) := by
    rw [hk]; exact hf.smul_measure (by simp)
  refine ⟨?_, (k : ℝ), ?_⟩
  · exact (hme.integrable_map_iff).1 hfm
  · have h1 : ∫ g, f g ∂(Measure.map j P) = ∫ y, f (j y) ∂P := hme.integral_map f
    rw [← h1, hk, integral_smul_nnreal_measure]
    simp [NNReal.smul_def]
