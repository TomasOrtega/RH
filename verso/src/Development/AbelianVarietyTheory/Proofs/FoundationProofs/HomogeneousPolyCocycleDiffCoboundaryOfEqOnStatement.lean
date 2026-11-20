import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomogeneousPolyCocycleDiffCoboundaryOfEqOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHomogeneousPolyCocycleDiffCoboundaryOfEqOn.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.homogeneousPolyCocycle_diff_coboundary_of_eqOn : ∀ (N l w n : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ z z' : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)), IsCoc w (Gam N l) z → IsCoc w (Gam N l) z' → Near z z' → ∃ p : MvPolynomial (Fin 2) (ZMod (l ^ n)), p.IsHomogeneous w ∧ ∀ γ ∈ Gam N l, z γ - z' γ = slP (γ : Matrix (Fin 2) (Fin 2) ℤ) p - p := by
  first | exact @GlobalTheory.KZ.H3.adj_of_near | exact GlobalTheory.KZ.H3.adj_of_near | (intros; apply GlobalTheory.KZ.H3.adj_of_near <;> assumption)
