import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthDecomposition
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.sixth_decomposition : CentredStringDecomposition := by
  first | exact @GlobalTheory.StringDecomp.stringDecomp_holds | exact GlobalTheory.StringDecomp.stringDecomp_holds | (intros; apply GlobalTheory.StringDecomp.stringDecomp_holds <;> assumption)
