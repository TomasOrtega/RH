import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.MeasurableSetUS
import GroundTheory.GlobalFields.IdeleGroups.Rational
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal

/- English proof (translation)
Use `le_antisymm ha ?_` and prove the remaining obligations. Use `mul_le_mul' (le_refl a) hb` as an intermediate fact. Rewrite `this` using `[h, mul_one]`. Then use the resulting hypothesis.
-/
private lemma eq_one_of_mul' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

/- English proof (translation)
Take `⟨h1, h2⟩` from `RationalIdeles.mem_positiveSubgroup.1 hy`. Rewrite `hm` using `[IdeleGroup.ideleModule_apply, IdeleGroup.finiteModule_eq_one_of_mem h1, mul_one, IdeleGroup.infiniteModule, Fintype.prod_unique, InfinitePlace.IsReal.mult_eq_one (RationalIdeles.isReal_infinitePlace default), pow_one]`. Use `⟨?_, fun v => ?_⟩` and prove the remaining obligations. Establish `hn : ‖(RationalIdeles.realPart y : ℝ)‖ = 1`. Rewrite using `[RationalIdeles.coe_realPart, RationalIdeles.realEquiv_apply, ← hm]`.

Conclude with `(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).norm_map_of_map_zero (map_zero _) _`. Rewrite `hn` using `[Real.norm_eq_abs, abs_of_pos h2, RationalIdeles.coe_realPart]`. Conclude with `RationalIdeles.realEquiv.injective (hn.trans (map_one _).symm)`. Take `⟨ha, hb⟩` from `(IdeleGroup.mem_standardOpenSubgroup ℚ).1 h1 v`. Use `eq_one_of_mul' ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha) ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb) ?_` and prove the remaining obligations.

Rewrite using `[← map_mul]`. Establish `h` using `congrArg (fun x : NumberField.AdeleRing (𝓞 ℚ) ℚ => x.2 v) (Units.mul_inv y)`. Establish `h' : (y : NumberField.AdeleRing (𝓞 ℚ) ℚ).2 v * ((y⁻¹ : IdeleGroup ℚ) : NumberField.AdeleRing (𝓞 ℚ) ℚ).2 v = 1` using `h`. Conclude with `(congrArg _ h').trans (map_one _)`.
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
Introduce `x`. Take `⟨⟨q, y⟩, hq⟩` from `RationalIdeles.mulMap_bijective.2 (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ)))`. Rewrite `hq` using `[RationalIdeles.mulMap_apply]`. Simplify using `only at hq`. Establish `hx` using `GroundTheory.Automorphic.Reduction.mem_normOneGL.1 x.2`.

Rewrite `hx` using `[← hq, map_mul, IdeleGroup.ideleModule_diagonal, one_mul]`. Establish `hy : (y : IdeleGroup ℚ) ∈ UU` using `mem_UU_of_pos y.2 hx`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : ∃ r : GL (Fin 2) ℚ, Matrix.GeneralLinearGroup.det r = q⁻¹ := by`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, ((q⁻¹ : ℚˣ) : ℚ)] ?_, Units.ext ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.det_fin_two_of]`.

Simplify using `[Matrix.det_fin_two_of]`. Establish `h : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r) = IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r)`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[GroundTheory.Automorphic.AdelicGLn.coe_det, IdeleGroup.coe_diagonal]`. Conclude with `(RingHom.map_det (algebraMap ℚ (NumberField.AdeleRing (𝓞 ℚ) ℚ)) (r : Matrix (Fin 2) (Fin 2) ℚ)).symm`.

Use `⟨⟨⟨GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r, GroundTheory.Automorphic.Reduction.rationalGL_le_normOneGL ⟨r, rfl⟩⟩, ⟨r, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[range_pm]`. Express the relevant statement in the definitionally equal form `GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r * (x : GL (Fin 2) (A ℚ))) ∈ UU`. Rewrite using `[map_mul, h, hr, ← hq, map_inv, inv_mul_cancel_left]`. Conclude with `hy`.
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
