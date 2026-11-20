import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig

open PositivityTheory.Rg.BcB.F.Eig

namespace GlobalTheory.CompanionTheory.BlockScalars

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem diagOp_apply {ι : Type} {d : ℕ} (blk : Fin d → ι) (c : ι → ℂ)
    (x : EuclideanSpace ℂ (Fin d)) (j : Fin d) :
    (diagOp blk c x) j = c (blk j) * x j := by
  simp [diagOp, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Use symmetry to reverse the relation.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem diagAlg : DiagAlg := by
  intro ι d blk c c' z
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x j
    simp [diagOp_apply, ContinuousLinearMap.mul_def, mul_assoc]
  · ext x j
    simp [diagOp_apply, add_mul]
  · ext x j
    simp [diagOp_apply]
  · rw [ContinuousLinearMap.star_eq_adjoint]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    simp only [PiLp.inner_apply, diagOp_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [RCLike.inner_apply]
    ring

end GlobalTheory.CompanionTheory.BlockScalars
