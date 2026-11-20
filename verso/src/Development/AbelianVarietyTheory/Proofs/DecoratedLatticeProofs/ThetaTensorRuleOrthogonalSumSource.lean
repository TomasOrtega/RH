import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsSumUniformLimitProductSpanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariableKeepsThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilTensorRuleScalarEqOneStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.TensorSrc

/- English proof (translation)
Establish `h1 : ∀ u', M (fun v' => f u' * g v') v = M g v * f u'`. Introduce `u'`. Establish `: (fun v' => f u' * g v') = f u' • g` using `by funext v'; simp`. Rewrite using `[this, map_smul]`. Simplify using `[mul_comm]`.

Establish `h2 : (fun u' => M (fun v' => f u' * g v') v) = M g v • f`. Use function extensionality and compare the values at `u'`. Simplify using `[h1]`. Rewrite using `[h2, map_smul]`. Simplify using `[mul_comm]`.
-/
theorem op_prod {X Y : Type} (L : Module.End ℂ (X → ℂ)) (M : Module.End ℂ (Y → ℂ)) (f : X → ℂ) (g : Y → ℂ) (u : X)
    (v : Y) : L (fun u' => M (fun v' => f u' * g v') v) u = L f u * M g v := by
  have h1 : ∀ u', M (fun v' => f u' * g v') v = M g v * f u' := by
    intro u'
    have : (fun v' => f u' * g v') = f u' • g := by funext v'; simp
    rw [this, map_smul]; simp [mul_comm]
  have h2 : (fun u' => M (fun v' => f u' * g v') v) = M g v • f := by
    funext u'; simp [h1]
  rw [h2, map_smul]; simp [mul_comm]

/- English proof (translation)
Introduce `D ψ hψ S A B d T`. Take `⟨h1, h2, h3, h4⟩` from `GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T d`. Establish `hb : ∀ fA fB u v, d.boxS T fA fB ((d.resS T).symm (u, v)) = fA u * fB v`. Introduce `fA fB u v`. Simplify using `[OrthDec.boxS]`.

Use `⟨h1, h2, h3, h4, GlobalTheory.T.thetaFunctions_sum_uniform_limit_product_span D ψ hψ S A B T d, ?_, ?_⟩` and prove the remaining obligations. Introduce `χA χB χT omS omA omB hS hA hB a b h fA fB hfA hfB`. Use function extensionality and compare the values at `x`. Take `⟨⟨u, v⟩, rfl⟩` from `(d.resS T).symm.surjective x`. Rewrite using `[GlobalTheory.T.weilTensorRule_scalar_eq_one D ψ S A B T d χA χB χT omS omA omB hS hA hB a b h _ (h1 fA fB hfA hfB) u v, hb]`.

Simplify using `only [hb]`. Conclude with `op_prod _ _ fA fB u v`. Introduce `χA χB χT omS omA omB hS hA hB a b h f hf v`. Use `⟨?_, fun u => GlobalTheory.T.weilTensorRule_scalar_eq_one D ψ S A B T d χA χB χT omS omA omB hS hA hB a b h f hf u v⟩` and prove the remaining obligations. Use `(h4 _ ((GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T d f hf).2 χB χT omB hB (b, h))).1 v` as an intermediate fact.

Simplify using `using this`.
-/
theorem tensorSource : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S A B : HSp D) (d : OrthDec S A B) (T : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.TensorSource ψ d T := by
  intro D ψ hψ S A B d T
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T d
  have hb : ∀ fA fB u v, d.boxS T fA fB ((d.resS T).symm (u, v)) = fA u * fB v := by
    intro fA fB u v
    simp [OrthDec.boxS]
  refine ⟨h1, h2, h3, h4, GlobalTheory.T.thetaFunctions_sum_uniform_limit_product_span D ψ hψ S A B T d, ?_, ?_⟩
  · intro χA χB χT omS omA omB hS hA hB a b h fA fB hfA hfB
    funext x
    obtain ⟨⟨u, v⟩, rfl⟩ := (d.resS T).symm.surjective x
    rw [GlobalTheory.T.weilTensorRule_scalar_eq_one D ψ S A B T d χA χB χT omS omA omB hS hA hB a b h _ (h1 fA fB hfA hfB) u v, hb]
    simp only [hb]
    exact op_prod _ _ fA fB u v
  · intro χA χB χT omS omA omB hS hA hB a b h f hf v
    refine ⟨?_, fun u => GlobalTheory.T.weilTensorRule_scalar_eq_one D ψ S A B T d χA χB χT omS omA omB hS hA hB a b h f hf u v⟩
    have := (h4 _ ((GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T d f hf).2 χB χT omB hB (b, h))).1 v
    simpa using this

end GlobalTheory.TensorSrc
