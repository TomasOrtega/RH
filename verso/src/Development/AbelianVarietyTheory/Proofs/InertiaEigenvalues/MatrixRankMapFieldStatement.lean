import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixRankMapField
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMatrixRankMapField.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.rank_map_ringHom : ∀ {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : ℕ} (M : Matrix (Fin n) (Fin n) K), (M.map φ).rank = M.rank := by
  first | exact @GlobalTheory.matrix_rank_map_field | exact GlobalTheory.matrix_rank_map_field | (intros; apply GlobalTheory.matrix_rank_map_field <;> assumption)
