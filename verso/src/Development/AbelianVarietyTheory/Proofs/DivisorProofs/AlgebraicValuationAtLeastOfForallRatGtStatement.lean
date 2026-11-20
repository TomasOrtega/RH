import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastOfForallRatGt
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QFam.sz_of_forall_rat_gt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAlgebraicValuationAtLeastOfForallRatGt.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.algebraicValuationAtLeast_of_forall_rat_gt : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (r : ℝ) (x : ℂ), (∀ q : ℚ, r < q → Sz l lam q x) → Sz l lam r x := by
  first | exact @GlobalTheory.QFam.sz_of_forall_rat_gt | exact GlobalTheory.QFam.sz_of_forall_rat_gt | (intros; apply GlobalTheory.QFam.sz_of_forall_rat_gt <;> assumption)
