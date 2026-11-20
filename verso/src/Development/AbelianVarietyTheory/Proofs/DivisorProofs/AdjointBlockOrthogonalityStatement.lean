import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointBlockOrthogonality
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SteepMult.AdPCasimir.sum_adP_mul_adP` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdjointBlockOrthogonality.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.adjoint_block_orthogonality : ∀ (R S : ℕ) (z w : NC R S), ∑ a : Ix R S, ∑ b : Ix R S, (if sameBlock a b then ∑ y : NC R S, (starRingEnd ℂ) (adP (Eab b a) y z) * adP (Eab b a) y w else 0) = if z = w then ((R + S : ℕ) : ℂ) else 0 := by
  first | exact @GlobalTheory.SteepMult.AdPCasimir.sum_adP_mul_adP | exact GlobalTheory.SteepMult.AdPCasimir.sum_adP_mul_adP | (intros; apply GlobalTheory.SteepMult.AdPCasimir.sum_adP_mul_adP <;> assumption)
