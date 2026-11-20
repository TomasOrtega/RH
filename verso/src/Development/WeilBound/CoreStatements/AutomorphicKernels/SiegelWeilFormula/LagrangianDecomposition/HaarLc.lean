import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicGLMulVecHaarEqModulusDet

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.ModuLR GlobalTheory.GaugeEx GlobalTheory.JacSubst

namespace PositivityTheory.SiegelWeilFormula.Ald

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm m J hJ bs g μ hμ f`. Use `letI mA : MeasurableSpace (Fin m × Fin 2 → AF F) := borel _`. Use `haveI : BorelSpace (Fin m × Fin 2 → AF F) := ⟨rfl⟩`. Use `letI mV : MeasurableSpace (Fin m → AE F E) := borel _`. Use `haveI : BorelSpace (Fin m → AE F E) := ⟨rfl⟩`.

Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)`. Set `e` to `coordCE F E (Module.finBasis F E)`. Use `haveI : LocallyCompactSpace (AE F E) := e.isOpenEmbedding.locallyCompactSpace`. Use `haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology`.

Use `haveI : T2Space (AE F E) := e.isEmbedding.t2Space`. Use `haveI : LocallyCompactSpace (Matrix (Fin m) (Fin 1) (AE F E)) := inferInstanceAs (LocallyCompactSpace (Fin m → Fin 1 → AE F E))`. Use `haveI : SecondCountableTopology (Matrix (Fin m) (Fin 1) (AE F E)) := inferInstanceAs (SecondCountableTopology (Fin m → Fin 1 → AE F E))`. Use `letI : MeasurableSpace (Matrix (Fin m) (Fin 1) (AE F E)) := borel _`. Use `haveI : BorelSpace (Matrix (Fin m) (Fin 1) (AE F E)) := ⟨rfl⟩`.

Use `set t : GL (Fin m) (AE F E) := (g : GL (Fin m) (AE F E)) with ht`. Establish `hdt : IsUnit (t : Matrix (Fin m) (Fin m) (AE F E)).det`. Rewrite using `[← Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `Units.isUnit _`. Set `φ` to `mulVecCE (t : Matrix (Fin m) (Fin m) (AE F E)) hdt`.

Take `⟨κ, _, _, Λ, hΛ, hdet, hχ⟩` from `@exists_matrix_restrictScalars_lrCE F E _ _ _ _ _ m (1 : ℕ) _ _ _ _ t (1 : GL (Fin 1) (AE F E))`. Establish `hc : addEquivAddHaarChar φ = 1`. Establish `h1 : addEquivAddHaarChar φ = addEquivAddHaarChar (lrCE t (1 : GL (Fin 1) (AE F E)))`. Rewrite using `[← addEquivAddHaarChar_transport (colCE (AE F E) m) φ]`. Use `congr 1`.

Use extensionality with `M i j`. Rewrite using `[Fin.fin_one_eq_zero j]`. Use `show ((t : Matrix (Fin m) (Fin m) (AE F E)) *ᵥ (fun k => M k 0)) i = ((t : Matrix (Fin m) (Fin m) (AE F E)) * M * ((1 : GL (Fin 1) (AE F E)) : Matrix (Fin 1) (Fin 1) (AE F E))) i 0`. Rewrite using `[Units.val_one, Matrix.mul_one]`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.mul_apply]`.

Establish `hu : hΛ.unit = Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)`. Use `ext`. Simplify using `only [IsUnit.unit_spec, hdet, Units.coe_map, MonoidHom.coe_coe, map_one, one_pow, mul_one, pow_one]`. Rewrite using `[h1, hχ, chi_AF_det, hu, ht, norm_det_unitary hcm hJ g, map_one]`. Establish `hV : ∀ (ν : Measure (Fin m → AE F E)), ν.IsAddHaarMeasure → ν.map φ = ν`.

Introduce `ν hν`. Use `haveI : ν.Regular := inferInstance`. Establish `key` using `addEquivAddHaarChar_smul_map ν φ`. Rewrite `key` using `[hc, one_smul]`. Then use the resulting hypothesis. Set `cm : (Fin m × Fin 2 → AF F) ≃ᵐ (Fin m → AE F E)` to `(colv m bs).toHomeomorph.toMeasurableEquiv`.

Set `pm : (Fin m → AE F E) ≃ᵐ (Fin m → AE F E)` to `φ.toHomeomorph.toMeasurableEquiv`. Use `haveI : μ.IsAddHaarMeasure := hμ`. Establish `hH : (μ.map cm).IsAddHaarMeasure` using `ContinuousAddEquiv.isAddHaarMeasure_map μ (colv m bs)`. Establish `hmap : (μ.map cm).map pm = μ.map cm` using `hV _ hH`. Establish `e1 : ∀ x, Lc bs (mat g) x = cm.symm (pm (cm x))` using `fun x => by rw [Lc_eq_colv]; rfl`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem haarLc : HaarLc := by
  intro F E _ _ _ _ _ σ hcm m J hJ bs g μ hμ f
  letI mA : MeasurableSpace (Fin m × Fin 2 → AF F) := borel _
  haveI : BorelSpace (Fin m × Fin 2 → AF F) := ⟨rfl⟩
  letI mV : MeasurableSpace (Fin m → AE F E) := borel _
  haveI : BorelSpace (Fin m → AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  let e := coordCE F E (Module.finBasis F E)
  haveI : LocallyCompactSpace (AE F E) := e.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin m) (Fin 1) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin m → Fin 1 → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin m) (Fin 1) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin 1 → AE F E))
  letI : MeasurableSpace (Matrix (Fin m) (Fin 1) (AE F E)) := borel _
  haveI : BorelSpace (Matrix (Fin m) (Fin 1) (AE F E)) := ⟨rfl⟩
  set t : GL (Fin m) (AE F E) := (g : GL (Fin m) (AE F E)) with ht
  have hdt : IsUnit (t : Matrix (Fin m) (Fin m) (AE F E)).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
  let φ := mulVecCE (t : Matrix (Fin m) (Fin m) (AE F E)) hdt
  obtain ⟨κ, _, _, Λ, hΛ, hdet, hχ⟩ :=
    @exists_matrix_restrictScalars_lrCE F E _ _ _ _ _ m (1 : ℕ) _ _ _ _ t (1 : GL (Fin 1) (AE F E))

  have hc : addEquivAddHaarChar φ = 1 := by
    have h1 : addEquivAddHaarChar φ = addEquivAddHaarChar (lrCE t (1 : GL (Fin 1) (AE F E))) := by
      rw [← addEquivAddHaarChar_transport (colCE (AE F E) m) φ]
      congr 1
      ext M i j
      rw [Fin.fin_one_eq_zero j]
      show ((t : Matrix (Fin m) (Fin m) (AE F E)) *ᵥ (fun k => M k 0)) i =
        ((t : Matrix (Fin m) (Fin m) (AE F E)) * M * ((1 : GL (Fin 1) (AE F E)) : Matrix (Fin 1) (Fin 1) (AE F E))) i 0
      rw [Units.val_one, Matrix.mul_one]
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    have hu : hΛ.unit = Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t) := by
      ext
      simp only [IsUnit.unit_spec, hdet, Units.coe_map, MonoidHom.coe_coe, map_one, one_pow, mul_one, pow_one]
    rw [h1, hχ, chi_AF_det, hu, ht, norm_det_unitary hcm hJ g, map_one]

  have hV : ∀ (ν : Measure (Fin m → AE F E)), ν.IsAddHaarMeasure → ν.map φ = ν := by
    intro ν hν
    haveI : ν.Regular := inferInstance
    have key := addEquivAddHaarChar_smul_map ν φ
    rwa [hc, one_smul] at key

  let cm : (Fin m × Fin 2 → AF F) ≃ᵐ (Fin m → AE F E) := (colv m bs).toHomeomorph.toMeasurableEquiv
  let pm : (Fin m → AE F E) ≃ᵐ (Fin m → AE F E) := φ.toHomeomorph.toMeasurableEquiv
  haveI : μ.IsAddHaarMeasure := hμ
  have hH : (μ.map cm).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ (colv m bs)
  have hmap : (μ.map cm).map pm = μ.map cm := hV _ hH
  have e1 : ∀ x, Lc bs (mat g) x = cm.symm (pm (cm x)) := fun x => by rw [Lc_eq_colv]; rfl
  calc ∫⁻ x, f (Lc bs (mat g) x) ∂μ = ∫⁻ x, (fun y => f (cm.symm (pm y))) (cm x) ∂μ := by simp_rw [e1]
    _ = ∫⁻ y, f (cm.symm (pm y)) ∂(μ.map cm) := (lintegral_map_equiv (fun y => f (cm.symm (pm y))) cm).symm
    _ = ∫⁻ y, f (cm.symm y) ∂((μ.map cm).map pm) := (lintegral_map_equiv (fun y => f (cm.symm y)) pm).symm
    _ = ∫⁻ y, f (cm.symm y) ∂(μ.map cm) := by rw [hmap]
    _ = ∫⁻ x, f (cm.symm (cm x)) ∂μ := lintegral_map_equiv (fun y => f (cm.symm y)) cm
    _ = ∫⁻ x, f x ∂μ := by simp

end PositivityTheory.SiegelWeilFormula.Ald

end
