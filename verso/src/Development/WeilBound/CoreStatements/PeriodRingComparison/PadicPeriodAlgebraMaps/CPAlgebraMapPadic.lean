import Mathlib
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.AcrisNAlgebraMapAinf
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Period
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Embedding
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul

noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

def cP : Reformulated.AutPerF.BdRPlus l (OC l) ≃+* Formalism.Per6.BdRp l :=
  Reformulated.AutPerF.BdRPlus.mapEquiv l (e l)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cP_apply (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    cP l y = Reformulated.AutPerF.BdRPlus.map l (e l).toRingHom y := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem comparison_algebraMap_ainf (a : Reformulated.AutPerF.Ainf l (OC l)) :
    cP l (algebraMap _ (Reformulated.AutPerF.BdRPlus l (OC l)) a) = Formalism.Per6.aD l a := by
  rw [cP_apply, Reformulated.AutPerF.BdRPlus.map_algebraMap_ainf, ainfMap_eq]
  rfl

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem awayEquiv_awayMap (z : Localization.Away ((l : ℕ) : OC l)) :
    IsPerfectoidField.awayEquiv (K := ℂ_[l]) l (Reformulated.AutPerF.awayMap l (e l).toRingHom z) =
      Reformulated.AutPerF.IsUnitBall.awayEquiv (PadicComplexInt l) l z := by
  have h : (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).toRingEquiv.toRingHom.comp
      (Reformulated.AutPerF.awayMap l (e l).toRingHom) =
      (Reformulated.AutPerF.IsUnitBall.awayEquiv (PadicComplexInt l) l).toRingEquiv.toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers ((l : ℕ) : OC l)) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply]
    rw [Reformulated.AutPerF.awayMap_algebraMap]
    change IsPerfectoidField.awayEquiv (K := ℂ_[l]) l (algebraMap (NC l) _ (e l x)) =
      Reformulated.AutPerF.IsUnitBall.awayEquiv (PadicComplexInt l) l (algebraMap (OC l) _ x)
    rw [AlgEquiv.commutes, Reformulated.AutPerF.IsUnitBall.awayEquiv_algebraMap]
    rfl
  exact RingHom.congr_fun h z

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem θD_cP (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    Formalism.Per6.θD l (cP l y) = Reformulated.AutPerF.BdRPlus.thetaC l (PadicComplexInt l) y := by
  change IsPerfectoidField.awayEquiv (K := ℂ_[l]) l
      (Reformulated.AutPerF.BdRPlus.theta l (NC l) (Reformulated.AutPerF.BdRPlus.map l (e l).toRingHom y)) = _
  rw [Reformulated.AutPerF.BdRPlus.theta_map, Reformulated.AutPerF.BdRPlus.thetaC_apply]
  exact awayEquiv_awayMap l _

end Cmp6
