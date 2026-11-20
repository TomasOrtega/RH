import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictLowerMemClosureTransvection
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.one_add_strictLower_mem_closure_transvection` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FOneAddStrictLowerMemClosureTransvection.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.one_add_strictLower_mem_closure_transvection' : ∀ (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R), (∀ a b, a ≤ b → c a b = 0) → 1 + c ∈ Submonoid.closure {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  first | exact @GlobalTheory.one_add_strictLower_mem_closure_transvection | exact GlobalTheory.one_add_strictLower_mem_closure_transvection | (intros; apply GlobalTheory.one_add_strictLower_mem_closure_transvection <;> assumption)
