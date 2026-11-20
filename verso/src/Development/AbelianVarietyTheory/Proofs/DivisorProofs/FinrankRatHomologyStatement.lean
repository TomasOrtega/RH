import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRatHomology
import Mathlib
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RatHomology.finrank_rat_homology` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinrankRatHomology.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.finrank_rat_homology_eq_finrank_int : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ), Module.Finite ℤ (C.homology n) → Module.finrank ℚ ((((ModuleCat.extendScalars (Int.castRingHom ℚ)).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) = Module.finrank ℤ (C.homology n) := by
  first | exact @GlobalTheory.RatHomology.finrank_rat_homology | exact GlobalTheory.RatHomology.finrank_rat_homology | (intros; apply GlobalTheory.RatHomology.finrank_rat_homology <;> assumption)
