import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueAlgebraicPolynomialDivisible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5 Polynomial
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FResidueAlgebraicPolynomialDivisible.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.residue_algebraic_polynomial_divisible : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (v : Valuation Ωl ℝ≥0), (∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) → v (p : Ωl) < 1 → ∀ (y : Ωl) (b : O0 p), IsAlgebraic ℤ y → v y ≤ 1 → v (y - algebraMap (O0 p) Ωl b) < 1 → ∃ P : ℤ[X], P.map (Int.castRingHom (ZMod p)) ≠ 0 ∧ (p : O0 p) ∣ aeval b P := by
  first | exact @GlobalTheory.K5.exists_int_poly_root_mod_p | exact GlobalTheory.K5.exists_int_poly_root_mod_p | (intros; apply GlobalTheory.K5.exists_int_poly_root_mod_p <;> assumption)
