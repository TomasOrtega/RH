import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviWhittakerEqOneOfCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinGL.LeviWh.leviWh_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLeviWhittakerEqOneOfCuspidal.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.levi_whittaker_eq_one_of_cuspidal : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → leviWh ψ b σ = 1 := by
  first | exact @GlobalTheory.FinGL.LeviWh.leviWh_eq_one | exact GlobalTheory.FinGL.LeviWh.leviWh_eq_one | (intros; apply GlobalTheory.FinGL.LeviWh.leviWh_eq_one <;> assumption)
