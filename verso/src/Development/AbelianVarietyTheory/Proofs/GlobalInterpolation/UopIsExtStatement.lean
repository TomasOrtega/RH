import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UopIsExt
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LvT.uop_isExt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FUopIsExt.lean&line=123#L123)
-/
theorem _root_.GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (v : X.A.vT) (φ : Fn X i) (Φ : M.Pt → M.Val), M.IsExt φ Φ → M.IsExt (Uop X i v φ) (fun p => ∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, Φ p₁) := by
  first | exact @GlobalTheory.LvT.uop_isExt | exact GlobalTheory.LvT.uop_isExt | (intros; apply GlobalTheory.LvT.uop_isExt <;> assumption)
