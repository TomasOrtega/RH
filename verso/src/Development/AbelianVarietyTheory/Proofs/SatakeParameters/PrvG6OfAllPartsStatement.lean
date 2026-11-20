import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionG6OfAllParts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FConclusionG6OfAllParts.lean&line=256#L256)
-/
theorem _root_.GlobalTheory.T.conclusionG6_of_all_parts : CentredStringDecomposition → PurityStringWeight → HeckeCharEqOfLAdicRealisation → MuChar → EigenCharTwist → ResCount → Numerics → Rest → ∀ D : D7, SumRepresentations.admitted D → RbEx D → SumRepresentations.ConclusionG6 D := by
  first | exact @GlobalTheory.EigenPoint.mem_Z_and_cusp_of_steps | exact GlobalTheory.EigenPoint.mem_Z_and_cusp_of_steps | (intros; apply GlobalTheory.EigenPoint.mem_Z_and_cusp_of_steps <;> assumption)
