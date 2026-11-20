import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationRingModel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.ValRing.valRingModel | exact GlobalTheory.ValRing.valRingModel | (intros; apply GlobalTheory.ValRing.valRingModel <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.valuation_ring_model : ValRingModel := by
  first | exact @GlobalTheory.ValRing.valRingModel | exact GlobalTheory.ValRing.valRingModel | (intros; apply GlobalTheory.ValRing.valRingModel <;> assumption)
