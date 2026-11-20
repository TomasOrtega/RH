import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBActDiagNatOneComm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGalBActDiagNatOneComm.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.galB_act_diagNatOne_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → ∀ (l : ℕ) [Fact l.Prime] (q : ℕ), 0 < q → ∀ (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l), X.galB l s (X.act l !![(q : ℤ), 0; 0, 1] b) = X.act l !![(q : ℤ), 0; 0, 1] (X.galB l s b) := by
  first | exact @GlobalTheory.KZ.Tower.galB_act_diag | exact GlobalTheory.KZ.Tower.galB_act_diag | (intros; apply GlobalTheory.KZ.Tower.galB_act_diag <;> assumption)
