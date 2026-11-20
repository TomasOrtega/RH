import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvUnitriangularMoveFrameMemFlagSubspace
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FInvUnitriangularMoveFrameMemFlagSubspace.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.inv_unitriangular_move_frame_mem_flagSubspace : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} {T : E} (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V), (∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) → ∀ b : Fin (r + 1), a⁻¹ (frame F b) - frame F b ∈ Xflag F b.val := by
  first | exact @GlobalTheory.FlagInv.inv_moves | exact GlobalTheory.FlagInv.inv_moves | (intros; apply GlobalTheory.FlagInv.inv_moves <;> assumption)
