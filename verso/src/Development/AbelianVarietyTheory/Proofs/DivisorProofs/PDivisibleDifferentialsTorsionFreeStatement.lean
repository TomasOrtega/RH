import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleDifferentialsTorsionFree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPDivisibleDifferentialsTorsionFree.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.p_divisible_differentials_torsion_free : GlobalTheory.Published.PrismaticDieudonneHodge → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : GlobalTheory.PDivGroup p O) (c : O) (w : G.omega), c ≠ 0 → c • w = 0 → w = 0 := by
  first | exact @GlobalTheory.omega_eq_zero_of_smul_eq_zero | exact GlobalTheory.omega_eq_zero_of_smul_eq_zero | (intros; apply GlobalTheory.omega_eq_zero_of_smul_eq_zero <;> assumption)
