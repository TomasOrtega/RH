import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariableKeepsThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPairStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger (dagger dagger_dagger conjAdjoint)

namespace GlobalTheory.SliceTarget

variable {D : D7} {T A B : HSp D}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem pA_giA (o : OrthDec T A B) : o.pA ⬝ giA T = giA A ⬝ adj o.jA := by
  rw [o.pA_eq]
  simp only [Matrix.mul_assoc, gA_mul_giA, Matrix.mul_one]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem resT_dagger (o : OrthDec T A B) (S : HSp D) (y : WO T S) :
    o.resT S (dagger T S y) = (dagger A S (o.resS S y).1, dagger B S (o.resS S y).2) := by
  have hA := pA_giA o
  have hB : o.pB ⬝ giA T = giA B ⬝ adj o.jB := pA_giA o.symm
  simp only [OrthDec.resT_apply, OrthDec.resS_apply, dagger, adj_mul, cancel₂ hA, cancel₂ hB, Matrix.mul_assoc]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem dagger_resS_symm (o : OrthDec T A B) (S : HSp D) (u : WO A S) (v : WO B S) :
    dagger T S ((o.resS S).symm (u, v)) = (o.resT S).symm (dagger A S u, dagger B S v) := by
  rw [AddEquiv.eq_symm_apply, resT_dagger, AddEquiv.apply_symm_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Apply an available result and prove the equalities needed to match it to the conclusion.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T A B S : HSp D) (o : OrthDec T A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om S A), IsWeilDatumO ψ S A χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun u => F ((o.resT S).symm (u, (o.resT S x).2))) (o.resT S x).1 := by
  intro D ψ T A B S o F hF χ χ' om hom p
  have hd := (GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hom.std S T).2.2.1
  have h := (GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ T A B S o _ ((hd F).2 hF)).1 χ' χ (conjAdjoint om)
    (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S A χ χ' om hom) p.swap
  refine (hd _).1 ?_
  convert h using 1
  funext y
  show starRingEnd ℂ (om p (fun u => F ((o.resT S).symm (u, (o.resT S (dagger T S y)).2))) (o.resT S (dagger T S y)).1) =
    starRingEnd ℂ (om p (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S A) fun u => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) F ((o.resS S).symm (u, (o.resS S y).2)))
      (dagger A S (o.resS S y).1))
  have e : (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S A) fun u => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) F ((o.resS S).symm (u, (o.resS S y).2))) =
      fun u => F ((o.resT S).symm (u, dagger B S (o.resS S y).2)) := by
    funext u
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm, dagger_dagger, Complex.conj_conj]
  rw [resT_dagger, e]

end GlobalTheory.SliceTarget
