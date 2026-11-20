import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperEighthFibrePowerOver
import Mathlib
open AlgebraicGeometry CategoryTheory Limits

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsProperEighthFibrePowerOver.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.isProper_eighth_fibre_power_over : ∀ {T : Scheme.{0}} {B C : Over T} (pr : Fin 8 → (B ⟶ C)), (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a) → IsProper C.hom → IsProper B.hom := by
  first | exact @GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power | exact GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power | (intros; apply GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power <;> assumption)
