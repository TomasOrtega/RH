import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig

open PositivityTheory.Rg.BcB.F.Eig

namespace GlobalTheory.CompanionTheory.BlockScalars

/- English proof (translation)
Simplify using `[diagOp, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]`.
-/
theorem diagOp_apply {ι : Type} {d : ℕ} (blk : Fin d → ι) (c : ι → ℂ)
    (x : EuclideanSpace ℂ (Fin d)) (j : Fin d) :
    (diagOp blk c x) j = c (blk j) * x j := by
  simp [diagOp, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

/- English proof (translation)
Introduce `ι d blk c c' z`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x j`. Simplify using `[diagOp_apply, ContinuousLinearMap.mul_def, mul_assoc]`. Use extensionality with `x j`.

Simplify using `[diagOp_apply, add_mul]`. Use extensionality with `x j`. Simplify using `[diagOp_apply]`. Rewrite using `[ContinuousLinearMap.star_eq_adjoint]`. Use `symm`.

Rewrite using `[ContinuousLinearMap.eq_adjoint_iff]`. Introduce `x y`. Simplify using `only [PiLp.inner_apply, diagOp_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[RCLike.inner_apply]`.

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
