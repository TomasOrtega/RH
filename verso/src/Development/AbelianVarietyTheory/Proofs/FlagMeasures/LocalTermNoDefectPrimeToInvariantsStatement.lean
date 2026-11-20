import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermNoDefectPrimeToInvariants
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocNoDef.noDefect` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLocalTermNoDefectPrimeToInvariants.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.localTerm_noDefect_primeTo_invariants : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), (FP p).RelG (LocNG.theta (Z.M p)) → (FP p).PrimeTo → ∀ (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → ¬ LocNG.BBne (H := locH Z p) t := by
  first | exact @GlobalTheory.LocNoDef.noDefect | exact GlobalTheory.LocNoDef.noDefect | (intros; apply GlobalTheory.LocNoDef.noDefect <;> assumption)
