import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIsOpenIsCompactUnitaryIntegralPoints.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.isOpen_isCompact_unitaryIntegralPoints : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → IsOpen (KU σ n : Set (GU σ n)) ∧ IsCompact (KU σ n : Set (GU σ n)) := by
  first | exact @GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU | exact GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU | (intros; apply GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU <;> assumption)
