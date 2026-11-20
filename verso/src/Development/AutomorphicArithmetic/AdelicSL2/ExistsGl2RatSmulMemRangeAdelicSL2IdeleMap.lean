import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.MeasurableSetUS
import GroundTheory.GlobalFields.IdeleGroups.Rational
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
private lemma eq_one_of_mul' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
private lemma mem_UU_of_pos {y : IdeleGroup ℚ} (hy : y ∈ RationalIdeles.positiveSubgroup)
    (hm : (IdeleGroup.ideleModule ℚ y : ℝ) = 1) : y ∈ UU := by
  obtain ⟨h1, h2⟩ := RationalIdeles.mem_positiveSubgroup.1 hy
  rw [IdeleGroup.ideleModule_apply, IdeleGroup.finiteModule_eq_one_of_mem h1, mul_one,
    IdeleGroup.infiniteModule, Fintype.prod_unique,
    InfinitePlace.IsReal.mult_eq_one (RationalIdeles.isReal_infinitePlace default), pow_one] at hm
  refine ⟨?_, fun v => ?_⟩
  · have hn : ‖(RationalIdeles.realPart y : ℝ)‖ = 1 := by
      rw [RationalIdeles.coe_realPart, RationalIdeles.realEquiv_apply, ← hm]
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).norm_map_of_map_zero
        (map_zero _) _
    rw [Real.norm_eq_abs, abs_of_pos h2, RationalIdeles.coe_realPart] at hn
    exact RationalIdeles.realEquiv.injective (hn.trans (map_one _).symm)
  · obtain ⟨ha, hb⟩ := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 h1 v
    refine eq_one_of_mul' ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha)
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb) ?_
    rw [← map_mul]
    have h := congrArg (fun x : NumberField.AdeleRing (𝓞 ℚ) ℚ => x.2 v) (Units.mul_inv y)
    have h' : (y : NumberField.AdeleRing (𝓞 ℚ) ℚ).2 v *
        ((y⁻¹ : IdeleGroup ℚ) : NumberField.AdeleRing (𝓞 ℚ) ℚ).2 v = 1 := h
    exact (congrArg _ h').trans (map_one _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Simplify by unfolding definitions. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.exists_gl2Rat_smul_mem_range_adelicSL2IdeleMap :
    ∀ x : GG, ∃ γ : Ga, γ • x ∈ Set.range pm := by
  intro x
  obtain ⟨⟨q, y⟩, hq⟩ := RationalIdeles.mulMap_bijective.2
    (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ)))
  rw [RationalIdeles.mulMap_apply] at hq
  dsimp only at hq
  have hx := GroundTheory.Automorphic.Reduction.mem_normOneGL.1 x.2
  rw [← hq, map_mul, IdeleGroup.ideleModule_diagonal, one_mul] at hx
  have hy : (y : IdeleGroup ℚ) ∈ UU := mem_UU_of_pos y.2 hx
  obtain ⟨r, hr⟩ : ∃ r : GL (Fin 2) ℚ, Matrix.GeneralLinearGroup.det r = q⁻¹ := by
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, ((q⁻¹ : ℚˣ) : ℚ)] ?_, Units.ext ?_⟩
    · simp [Matrix.det_fin_two_of]
    · simp [Matrix.det_fin_two_of]
  have h : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r) =
      IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) := by
    refine Units.ext ?_
    rw [GroundTheory.Automorphic.AdelicGLn.coe_det, IdeleGroup.coe_diagonal]
    exact (RingHom.map_det (algebraMap ℚ (NumberField.AdeleRing (𝓞 ℚ) ℚ))
      (r : Matrix (Fin 2) (Fin 2) ℚ)).symm
  refine ⟨⟨⟨GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r,
    GroundTheory.Automorphic.Reduction.rationalGL_le_normOneGL ⟨r, rfl⟩⟩, ⟨r, rfl⟩⟩, ?_⟩
  rw [range_pm]
  change GroundTheory.Automorphic.AdelicGLn.det ℚ 2
    (GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r * (x : GL (Fin 2) (A ℚ))) ∈ UU
  rw [map_mul, h, hr, ← hq, map_inv, inv_mul_cancel_left]
  exact hy
