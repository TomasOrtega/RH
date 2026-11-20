import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorGramMatrixConstDoubleCoset
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLeadMinorGramMatrixConstDoubleCoset.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.leadMinor_gramMatrix_const_doubleCoset : ∀ (D : D7) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) (T T' : D.host.E) (F : LFlag (VS D) D.R.rS T) (F₁ F₂ : LFlag (VS D) D.R.rS T'), Formalism.L2.SG.TermDef.DCRel Λ F F₁ F₂ → ∀ l : ℕ, leadMinorE (ZhatL F F₂) l = leadMinorE (ZhatL F F₁) l := by
  first | exact @GlobalTheory.leadMinorE_zhatL_dcrel | exact GlobalTheory.leadMinorE_zhatL_dcrel | (intros; apply GlobalTheory.leadMinorE_zhatL_dcrel <;> assumption)
