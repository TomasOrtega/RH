import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
import Formalism.PieriBlockIdeals.PieriColumnMinors.RealLocalDeltaNabla

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

/- English proof (translation)
Establish `h : (blockRed O N ϖ τ).comp (rowAct O M) = ((blockSub (O ⧸ Ideal.span {ϖ}) N A).restrictScalars O).comp (blockRed O N ϖ τ)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, rowAct, blockRed, blockSub, aeval_X, map_sum, map_mul, hA, Matrix.map_apply]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[aeval_C]`. Both sides reduce to the same expression. Conclude with `congrArg (fun φ => φ f) h`.
-/
theorem blockRed_rowAct (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι)
    (A : ι → Matrix (Fin N) (Fin N) (O ⧸ Ideal.span {ϖ})) (M : Matrix (Fin N) (Fin N) O)
    (hA : A τ = M.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ (rowAct O M f) = blockSub (O ⧸ Ideal.span {ϖ}) N A (blockRed O N ϖ τ f) := by
  have h : (blockRed O N ϖ τ).comp (rowAct O M) =
      ((blockSub (O ⧸ Ideal.span {ϖ}) N A).restrictScalars O).comp (blockRed O N ϖ τ) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, rowAct, blockRed, blockSub, aeval_X, map_sum, map_mul,
      hA, Matrix.map_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    rw [aeval_C]
    rfl
  exact congrArg (fun φ => φ f) h

end GlobalTheory.HighWtEmb

/- English proof (translation)
Introduce `O _ N ι _ _ mu ϖ g y`. Proceed by induction on `y using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r m`. Rewrite using `[LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul]`. Establish `h1` using `(Formalism.CohomologicalDescent.RealLocalDeltaNabla.nabla_rep_tensor_product O ι (fun _ => N) (fun _ => N) (fun τ => res N (mu τ)) g m)`.

Simplify using `only [GlobalTheory.ExpFrame.grp]`. Rewrite using `[h1.1]`. Simplify using `only [redT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, map_prod, IsScalarTower.algebraMap_apply O (O ⧸ Ideal.span {ϖ}), AlgHom.commutes]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[h1.2 τ]`. Conclude with `blockRed_rowAct O N ϖ τ _ _ rfl _`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem GlobalTheory.HighWtEmb.redT_grp : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (g : ι → GL (Fin N) O) (y : NablaT O N mu), redT O N mu ϖ (grp O N mu g y) = blockSub (O ⧸ Ideal.span {ϖ}) N (fun τ => (((g τ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (redT O N mu ϖ y) := by
  intro O _ N ι _ _ mu ϖ g y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul]
    have h1 := (Formalism.CohomologicalDescent.RealLocalDeltaNabla.nabla_rep_tensor_product O ι (fun _ => N) (fun _ => N) (fun τ => res N (mu τ)) g m)
    simp only [GlobalTheory.ExpFrame.grp]
    rw [h1.1]
    simp only [redT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_prod, IsScalarTower.algebraMap_apply O (O ⧸ Ideal.span {ϖ}), AlgHom.commutes]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [h1.2 τ]
    exact blockRed_rowAct O N ϖ τ _ _ rfl _
  | add a b ha hb => simp only [map_add, ha, hb]

end
