import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianStdIsometryOfRationalIsometry
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FHermitianStdIsometryOfRationalIsometry.lean&line=132#L132)
-/
theorem _root_.GlobalTheory.T.hermitianStdIsometry_of_rationalIsometry : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D → GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.StdIsomSt D := by
  first | exact @GlobalTheory.StdIsom.stdIsomSt_of_rationalSt | exact GlobalTheory.StdIsom.stdIsomSt_of_rationalSt | (intros; apply GlobalTheory.StdIsom.stdIsomSt_of_rationalSt <;> assumption)
