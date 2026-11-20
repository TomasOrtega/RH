import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FCorrectionOfTransport.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.correctionSt_of_transportSt : ∀ D : D7, TransportSt D → CorrectionSt D := by
  first | exact @GlobalTheory.AdIsomCorrection.correction_of_transport | exact GlobalTheory.AdIsomCorrection.correction_of_transport | (intros; apply GlobalTheory.AdIsomCorrection.correction_of_transport <;> assumption)
