import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.ChiBasic

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ σ _ hp n _ v`. Take `⟨η, hη⟩` from `UpperTheory.ConvolutionTheory.R.classChar2 F E hp`. Establish `hpow` using `(UpperTheory.ConvolutionTheory.R.normCharPow_holds F E hp η hη).1`. Establish `key : ∀ g : Gw n v, g ∈ normSet E n v ↔ chiAt n η v g = 1`. Introduce `g`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `h η hη.1`. Simplify using `only [chiAt, h1, Units.val_one]`. Introduce `h χ hχ`.

Take `⟨j, -, -, rfl⟩` from `hpow χ hχ`. Establish `h1 : η.loc v (Matrix.GeneralLinearGroup.det g) = 1` using `Units.ext h`. Use `show (η ^ j).loc v (Matrix.GeneralLinearGroup.det g) = 1`. Establish `h2 : (η ^ j).loc v (Matrix.GeneralLinearGroup.det g) = (η.loc v (Matrix.GeneralLinearGroup.det g)) ^ j` using `rfl`. Rewrite using `[h2, h1, one_pow]`.

Use `⟨?_, fun γ x => ?_⟩` and prove the remaining obligations. Establish `hs : normSet E n v = chiAt n η v ⁻¹' {1}` using `Set.ext fun g => key g`. Rewrite using `[hs]`. Conclude with `((UpperTheory.Gal.InertialTypesAlt.G.chiBasic F n η v).1).isClopen_fiber 1`. Establish `hd : Matrix.GeneralLinearGroup.det (x⁻¹ * γ * x) = Matrix.GeneralLinearGroup.det γ`.

Rewrite using `[map_mul, map_mul, map_inv, mul_comm _ (Matrix.GeneralLinearGroup.det γ), mul_assoc, inv_mul_cancel, mul_one]`. Rewrite using `[key, key]`. Simplify using `only [chiAt, hd]`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.G.normOpen :
    UpperTheory.Gal.InertialTypesAlt.G.NormOpen := by
  intro F E _ _ _ _ _ _ _ _ σ _ hp n _ v
  obtain ⟨η, hη⟩ := UpperTheory.ConvolutionTheory.R.classChar2 F E hp
  have hpow := (UpperTheory.ConvolutionTheory.R.normCharPow_holds F E hp η hη).1
  have key : ∀ g : Gw n v, g ∈ normSet E n v ↔ chiAt n η v g = 1 := by
    intro g
    constructor
    · intro h
      have h1 := h η hη.1
      simp only [chiAt, h1, Units.val_one]
    · intro h χ hχ
      obtain ⟨j, -, -, rfl⟩ := hpow χ hχ
      have h1 : η.loc v (Matrix.GeneralLinearGroup.det g) = 1 := Units.ext h
      show (η ^ j).loc v (Matrix.GeneralLinearGroup.det g) = 1
      have h2 : (η ^ j).loc v (Matrix.GeneralLinearGroup.det g) = (η.loc v (Matrix.GeneralLinearGroup.det g)) ^ j := rfl
      rw [h2, h1, one_pow]
  refine ⟨?_, fun γ x => ?_⟩
  · have hs : normSet E n v = chiAt n η v ⁻¹' {1} := Set.ext fun g => key g
    rw [hs]
    exact ((UpperTheory.Gal.InertialTypesAlt.G.chiBasic F n η v).1).isClopen_fiber 1
  · have hd : Matrix.GeneralLinearGroup.det (x⁻¹ * γ * x) = Matrix.GeneralLinearGroup.det γ := by
      rw [map_mul, map_mul, map_inv, mul_comm _ (Matrix.GeneralLinearGroup.det γ), mul_assoc, inv_mul_cancel, mul_one]
    rw [key, key]
    simp only [chiAt, hd]
