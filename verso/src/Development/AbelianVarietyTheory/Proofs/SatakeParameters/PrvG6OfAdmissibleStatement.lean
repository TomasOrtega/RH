import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionG6OfAdmissible
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.ClosingSixth.conclusionG6_of_adm | exact GlobalTheory.ClosingSixth.conclusionG6_of_adm | (intros; apply GlobalTheory.ClosingSixth.conclusionG6_of_adm <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.conclusionG6_of_admissible : ∀ D : D7, SumRepresentations.admitted D → RbEx D → SumRepresentations.ConclusionG6 D := by
  first | exact @GlobalTheory.ClosingSixth.conclusionG6_of_adm | exact GlobalTheory.ClosingSixth.conclusionG6_of_adm | (intros; apply GlobalTheory.ClosingSixth.conclusionG6_of_adm <;> assumption)
