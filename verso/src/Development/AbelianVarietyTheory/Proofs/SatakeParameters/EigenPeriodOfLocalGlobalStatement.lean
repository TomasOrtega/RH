import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPeriodOfLocalGlobal
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TameEig.eigPd_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FEigenPeriodOfLocalGlobal.lean&line=163#L163)
-/
theorem _root_.GlobalTheory.T.eigen_period_of_local_global : ∀ D : D7, SumRepresentations.AdmA D → LGC D → RbEx D → EigPd D := by
  first | exact @GlobalTheory.TameEig.eigPd_holds | exact GlobalTheory.TameEig.eigPd_holds | (intros; apply GlobalTheory.TameEig.eigPd_holds <;> assumption)
