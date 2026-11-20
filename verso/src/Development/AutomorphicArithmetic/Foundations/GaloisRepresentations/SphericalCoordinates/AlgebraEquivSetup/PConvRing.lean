import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.W2.Seed.pConvRing :
    ConvRing := by
  intro X _ K hK f hf f' hf'
  refine ⟨Formalism.UG.Final.HeckeConvMem X K ℂ hK f hf f' hf', fun f'' hf'' => ?_⟩
  exact Formalism.UG.Final.HeckeAssoc X K ℂ hK f hf f' hf' f'' hf''
