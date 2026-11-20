import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachHypothesisCrystallineLattices
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWachHypothesisCrystallineLattices.lean&line=101#L101)
-/
theorem _root_.GlobalTheory.T.wachHypothesis_crystallineLattices : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantLattices.UsedLocalConclusion D HW F Cm → DeltaInvariantLattices.ConclusionE D HW F → CrysOnCond D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie := by
  first | exact @GlobalTheory.WachHyp.hypW_crystalline | exact GlobalTheory.WachHyp.hypW_crystalline | (intros; apply GlobalTheory.WachHyp.hypW_crystalline <;> assumption)
