import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsSameRowSameWeightSameLocalData
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FTermsSameRowSameWeightSameLocalData.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.terms_same_row_same_weight_same_localData : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', t.G ≠ 0 → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → Formalism.L2.SG.TermOp.wt t = Formalism.L2.SG.TermOp.wt t' ∧ (nmlOf Y u u' t = nmlOf Y u u' t' → ∀ (p : PlF D) (P : LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), P.RelG (LocNG.theta (Y.M p)) → ∀ d, Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 (Tu D u) (Tu D u')) → Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t'.toTerm.lam (lf D (X.Fu u)) (Quot.out t'.toTerm.cls).1 (Tu D u) (Tu D u'))) := by
  first | exact @GlobalTheory.LocOver.TermSame.same | exact GlobalTheory.LocOver.TermSame.same | (intros; apply GlobalTheory.LocOver.TermSame.same <;> assumption)
