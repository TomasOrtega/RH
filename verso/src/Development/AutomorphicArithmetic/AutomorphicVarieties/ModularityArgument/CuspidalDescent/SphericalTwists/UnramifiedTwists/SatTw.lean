import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.RowProps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Desc.W.satTw :
    UpperTheory.V.Z.Desc.W.SatTw := by
  intro E _ _ _ a P s w B h
  have h1 := (GlobalTheory.CuspRep.CG.HasSat.twist_absPow h s).1
  have h2 := (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s).2.1 w
  have h3 : GlobalTheory.WeilDeligne.qPow w (-s) = (GlobalTheory.HeckeGal.Model.absPow E s).val w := by
    refine Units.ext ?_
    rw [h2, GlobalTheory.WeilDeligne.coe_qPow]
    simp only [Formalism.ConjugateSelfDual.normV, Complex.ofReal_neg]
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h3]
  exact h1
