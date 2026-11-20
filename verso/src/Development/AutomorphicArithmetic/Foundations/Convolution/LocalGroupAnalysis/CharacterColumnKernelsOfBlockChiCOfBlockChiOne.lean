import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
open PositivityTheory.Rg.Tf.Geo
open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open scoped NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h : galAd σ = MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ`. Use `adeleRingHom_ext (K := F) (fun l => ?_) (fun a => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F]) ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] l))) = σ • algebraMap E 𝔸[E] l`. Rewrite using `[adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul, AdeleBaseChange.smul_algebraMap, map_one, map_one, mul_one]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F]) ((adeleTensorEquiv F E).symm (adeleMap F E a))) = σ • adeleMap F E a`. Rewrite using `[adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul, smul_adeleMap, map_one, map_one, one_mul]`. Both sides reduce to the same expression. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
private theorem galAd_apply (σ : E ≃ₐ[F] E) (y : 𝔸[E]) : galAd σ y = σ • y := by
  have h : galAd σ = MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ := by
    refine adeleRingHom_ext (K := F) (fun l => ?_) (fun a => ?_)
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] l))) = σ • algebraMap E 𝔸[E] l
      rw [adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        AdeleBaseChange.smul_algebraMap, map_one, map_one, mul_one]
      rfl
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (adeleMap F E a))) = σ • adeleMap F E a
      rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        smul_adeleMap, map_one, map_one, one_mul]
      rfl
  rw [h]
  rfl

/- English proof (translation)
Establish `hM : Topology.IsClosedEmbedding ((adeleMap F E).mapMatrix.toMonoidHom : Matrix (Fin n) (Fin n) 𝔸[F] → Matrix (Fin n) (Fin n) 𝔸[E])` using `Function.LeftInverse.isClosedEmbedding (f := fun M : Matrix (Fin n) (Fin n) 𝔸[E] => M.map (adeleRetraction F E)) (fun M => Matrix.ext fun i j => adeleRetraction_adeleMap (M i j)) (continuous_id.matrix_map continuous_adeleRetraction) (continuous_id.matrix_map continuous_adeleMap)`. Conclude with `@Topology.IsClosedEmbedding.units_map (AdelicGLn.AdelicMatrix F n) (AdelicGLn.AdelicMatrix E n) _ _ _ _ _ _ (adeleMap F E).mapMatrix.toMonoidHom hM`.
-/
private theorem closedEmb (n : ℕ) : Topology.IsClosedEmbedding
    (mapGL n (adeleMap F E) : AdelicGLn.AdelicGL F n → AdelicGLn.AdelicGL E n) := by
  have hM : Topology.IsClosedEmbedding
      ((adeleMap F E).mapMatrix.toMonoidHom : Matrix (Fin n) (Fin n) 𝔸[F] → Matrix (Fin n) (Fin n) 𝔸[E]) :=
    Function.LeftInverse.isClosedEmbedding (f := fun M : Matrix (Fin n) (Fin n) 𝔸[E] => M.map (adeleRetraction F E))
      (fun M => Matrix.ext fun i j => adeleRetraction_adeleMap (M i j))
      (continuous_id.matrix_map continuous_adeleRetraction)
      (continuous_id.matrix_map continuous_adeleMap)
  exact @Topology.IsClosedEmbedding.units_map (AdelicGLn.AdelicMatrix F n) (AdelicGLn.AdelicMatrix E n)
    _ _ _ _ _ _ (adeleMap F E).mapMatrix.toMonoidHom hM

/- English proof (translation)
The claim follows from `Units.ext ((adeleMap F E).map_det (g : Matrix (Fin n) (Fin n) 𝔸[F])).symm`.
-/
private theorem det_inc (n : ℕ) (g : AdelicGLn.AdelicGL F n) :
    AdelicGLn.det E n (mapGL n (adeleMap F E) g) = ideleEmbedding F E (AdelicGLn.det F n g) :=
  Units.ext ((adeleMap F E).map_det (g : Matrix (Fin n) (Fin n) 𝔸[F])).symm

/- English proof (translation)
The claim follows from `Units.ext ((((galAd σ).map_det (g : Matrix (Fin n) (Fin n) 𝔸[E])).symm).trans (galAd_apply σ _))`.
-/
private theorem det_gal (σ : E ≃ₐ[F] E) (n : ℕ) (g : AdelicGLn.AdelicGL E n) :
    AdelicGLn.det E n (mapGL n (galAd σ) g) = σ • (AdelicGLn.det E n g : IdeleGroup E) :=
  Units.ext ((((galAd σ).map_det (g : Matrix (Fin n) (Fin n) 𝔸[E])).symm).trans (galAd_apply σ _))

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ _ n _`. Use `⟨closedEmb n, fun g => ?_, fun g => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(IdeleGroup.ideleModule E (AdelicGLn.det E n (mapGL n (adeleMap F E) g)) : ℝ) = (IdeleGroup.ideleModule F (AdelicGLn.det F n g) : ℝ) ^ Module.finrank F E`. Rewrite using `[det_inc, ← EllipticTorus.ideleModule_ideleNorm (K := F), ideleNorm_ideleEmbedding, map_pow, Positive.val_pow]`. Express the relevant statement in the definitionally equal form `IdeleGroup.ideleModule E (AdelicGLn.det E n (mapGL n (galAd σ) g)) = IdeleGroup.ideleModule E (AdelicGLn.det E n g)`.

Rewrite using `[det_gal, ← EllipticTorus.ideleModule_ideleNorm (K := F), ideleNorm_smul, EllipticTorus.ideleModule_ideleNorm]`.
-/
theorem UpperTheory.ConvolutionTheory.G.character_column_kernels_of_block_chi_c_of_block_chi_one :
    N5 := by
  intro F E _ _ _ _ _ _ σ _ n _
  refine ⟨closedEmb n, fun g => ?_, fun g => ?_⟩
  · change (IdeleGroup.ideleModule E (AdelicGLn.det E n (mapGL n (adeleMap F E) g)) : ℝ) =
      (IdeleGroup.ideleModule F (AdelicGLn.det F n g) : ℝ) ^ Module.finrank F E
    rw [det_inc, ← EllipticTorus.ideleModule_ideleNorm (K := F), ideleNorm_ideleEmbedding, map_pow,
      Positive.val_pow]
  · change IdeleGroup.ideleModule E (AdelicGLn.det E n (mapGL n (galAd σ) g)) =
      IdeleGroup.ideleModule E (AdelicGLn.det E n g)
    rw [det_gal, ← EllipticTorus.ideleModule_ideleNorm (K := F), ideleNorm_smul,
      EllipticTorus.ideleModule_ideleNorm]
