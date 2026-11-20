import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayDataNonempty
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.RayEx.nonempty_rayData` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FRayDataNonempty.lean&line=158#L158)
-/
theorem _root_.GlobalTheory.T.ray_data_nonempty : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → Nonempty (RayData K M) := by
  first | exact @GlobalTheory.Mem.RayEx.nonempty_rayData | exact GlobalTheory.Mem.RayEx.nonempty_rayData | (intros; apply GlobalTheory.Mem.RayEx.nonempty_rayData <;> assumption)
