import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationRingModel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FValuationRingModel.lean&line=257#L257)
-/
theorem _root_.GlobalTheory.T.valuation_ring_model : ValRingModel := by
  first | exact @GlobalTheory.ValRing.valRingModel | exact GlobalTheory.ValRing.valRingModel | (intros; apply GlobalTheory.ValRing.valRingModel <;> assumption)
