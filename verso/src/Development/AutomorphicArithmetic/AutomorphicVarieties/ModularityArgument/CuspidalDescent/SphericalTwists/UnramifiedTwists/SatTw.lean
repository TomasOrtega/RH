import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.RowProps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow

/- English proof (translation)
Introduce `E _ _ _ a P s w B h`. Establish `h1` using `(GlobalTheory.CuspRep.CG.HasSat.twist_absPow h s).1`. Establish `h2` using `(GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s).2.1 w`. Establish `h3 : GlobalTheory.WeilDeligne.qPow w (-s) = (GlobalTheory.HeckeGal.Model.absPow E s).val w`. Use `Units.ext ?_` and prove the remaining obligations.

Rewrite using `[h2, GlobalTheory.WeilDeligne.coe_qPow]`. Simplify using `only [Formalism.ConjugateSelfDual.normV, Complex.ofReal_neg]`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Rewrite using `[h3]`. Conclude with `h1`.
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
