import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

/- English proof (translation)
Introduce `X _ K hK f hf f' hf'`. Use `⟨Formalism.UG.Final.HeckeConvMem X K ℂ hK f hf f' hf', fun f'' hf'' => ?_⟩` and prove the remaining obligations. Conclude with `Formalism.UG.Final.HeckeAssoc X K ℂ hK f hf f' hf' f'' hf''`.
-/
theorem UpperTheory.Gal.W2.Seed.pConvRing :
    ConvRing := by
  intro X _ K hK f hf f' hf'
  refine ⟨Formalism.UG.Final.HeckeConvMem X K ℂ hK f hf f' hf', fun f'' hf'' => ?_⟩
  exact Formalism.UG.Final.HeckeAssoc X K ℂ hK f hf f' hf' f'' hf''
