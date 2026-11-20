import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPadicCocycleOfCompatiblePolyFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsPadicCocycleOfCompatiblePolyFamily.lean&line=110#L110)
-/
theorem _root_.GlobalTheory.T.exists_padic_cocycle_of_compatible_poly_family : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ, IsFam l w (Gam N l) Φ → ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) ℤ_[l], IsCoc w (Gam N l) z ∧ ∀ n, Near (fun δ => MvPolynomial.map (PadicInt.toZModPow n) (z δ)) (Φ n) := by
  first | exact @GlobalTheory.KZ.H3.cocycle_lift_of_fam | exact GlobalTheory.KZ.H3.cocycle_lift_of_fam | (intros; apply GlobalTheory.KZ.H3.cocycle_lift_of_fam <;> assumption)
