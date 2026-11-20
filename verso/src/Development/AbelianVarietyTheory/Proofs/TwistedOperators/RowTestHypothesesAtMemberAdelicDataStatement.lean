import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHypothesesAtMemberAdelicData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PrimIn.rowTest_setting_dat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FRowTestHypothesesAtMemberAdelicData.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.hidaSetting_of_sizeRows : Ev fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), K.Over B.toPre → GrpTrue Z.N f → z.R.toRealDat.ExAt → ∀ L : SizeData₂ (w.st Z).toD7, GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L → GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 := by
  first | exact @GlobalTheory.PrimIn.rowTest_setting_dat | exact GlobalTheory.PrimIn.rowTest_setting_dat | (intros; apply GlobalTheory.PrimIn.rowTest_setting_dat <;> assumption)
