import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleNsmul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
open GlobalTheory GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ProjVar.Var.ample_nsmul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAmpleNsmul.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.ample_nsmul_of_pos : ∀ (F : Type) [Field F] (Y : Var F) (Δ : Y.Dv) (n : ℕ), 0 < n → Y.ample Δ → Y.ample (n • Δ) := by
  first | exact @GlobalTheory.ProjVar.Var.ample_nsmul | exact GlobalTheory.ProjVar.Var.ample_nsmul | (intros; apply GlobalTheory.ProjVar.Var.ample_nsmul <;> assumption)
