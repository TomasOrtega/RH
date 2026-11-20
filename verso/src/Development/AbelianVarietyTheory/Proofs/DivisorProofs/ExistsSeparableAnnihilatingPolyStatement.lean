import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparableAnnihilatingPoly
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSeparableAnnihilatingPoly.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_separable_annihilating_poly : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [CharZero C] (φ : ℤ_[p] →+* C) (Λ : Type) [CommRing Λ] [IsDomain Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (a : Λ), ∃ f : Polynomial ℤ_[p], Polynomial.aeval a f = 0 ∧ (f.map φ).Separable := by
  first | exact @GlobalTheory.exists_poly_aeval_eq_zero_map_separable | exact GlobalTheory.exists_poly_aeval_eq_zero_map_separable | (intros; apply GlobalTheory.exists_poly_aeval_eq_zero_map_separable <;> assumption)
