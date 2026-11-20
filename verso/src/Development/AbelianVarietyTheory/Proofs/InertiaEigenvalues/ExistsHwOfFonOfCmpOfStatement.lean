import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwOfFonOfCmpOf
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HWL.exists_hwOf_fonOf_cmpOf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsHwOfFonOfCmpOf.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_hwOf_fonOf_cmpOf' : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) → (∀ (l : ℕ) [Fact l.Prime], WachEx (A l)) → ∃ (H : HWOf L) (F : FonOf L A H), Nonempty (CmpOf L A H F) := by
  first | exact @GlobalTheory.HWL.exists_hwOf_fonOf_cmpOf | exact GlobalTheory.HWL.exists_hwOf_fonOf_cmpOf | (intros; apply GlobalTheory.HWL.exists_hwOf_fonOf_cmpOf <;> assumption)
