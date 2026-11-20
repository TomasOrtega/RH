import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPointRowAdmissibleTrueColumns
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PerQ.twistedPointIntegral_of_TC_ok` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FTwistedPointRowAdmissibleTrueColumns.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.twistedPointRow_admissible_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), Formalism.L2.G.Adm2InU.TwistedPointIntegral (I.rec7 l Z) (I.tw l l0 Z) := by
  first | exact @GlobalTheory.PerQ.twistedPointIntegral_of_TC_ok | exact GlobalTheory.PerQ.twistedPointIntegral_of_TC_ok | (intros; apply GlobalTheory.PerQ.twistedPointIntegral_of_TC_ok <;> assumption)
