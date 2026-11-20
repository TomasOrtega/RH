import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedValuationParitySignCharacterKernelNorm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtaChar.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnramifiedValuationParitySignCharacterKernelNorm.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ x y : F, x ≠ 0 → y ≠ 0 → eta (x * y) = eta x * eta y) ∧ (∀ x : F, ‖x‖ = 1 → eta x = 1) ∧ (∀ x : F, x ≠ 0 → (eta x = 1 ↔ ∃ v : E, v * star v = algebraMap F E x)) ∧ IsLocallyConstant (fun x : {x : F // x ≠ 0} => eta x.1) := by
  first | exact @GlobalTheory.EtaChar.main | exact GlobalTheory.EtaChar.main | (intros; apply GlobalTheory.EtaChar.main <;> assumption)
