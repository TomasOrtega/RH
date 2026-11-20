import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrMatrixProjPreimage
import Mathlib
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDvrMatrixProjPreimage.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.dvr_matrix_proj_preimage_alt : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (n : Type) [Fintype n] [DecidableEq n] (S : Submodule K (n → K)), ∃ P : Matrix n n O, (∀ v : n → O, (fun i => algebraMap O K ((P.mulVec v) i)) ∈ S) ∧ ∀ u : n → O, (fun i => algebraMap O K (u i)) ∈ S → P.mulVec u = u := by
  first | exact @GlobalTheory.dvr_matrix_proj_preimage | exact GlobalTheory.dvr_matrix_proj_preimage | (intros; apply GlobalTheory.dvr_matrix_proj_preimage <;> assumption)
