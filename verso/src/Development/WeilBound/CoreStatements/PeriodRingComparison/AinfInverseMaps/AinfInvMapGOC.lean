import Mathlib
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.AcrisNAlgebraMapAinf
import Development.WeilBound.CoreStatements.PeriodRingComparison.AinfAlgebraMaps.CAAlgebraMapGOC
import Development.WeilBound.CoreStatements.PeriodRingComparison.PadicPeriodAlgebraMaps.CPAlgebraMapPadic
import Development.WeilBound.CoreStatements.PeriodRingComparison.ThetaKernelDeRham.KerThetaEqSpanSymmTBdR
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.PhiGalCris

noncomputable section

open GroundTheory.PAdicHodge
open Formalism.BasicNotions.Loc (GQ)

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem ainfInv_map_gOC (g : GQ l) (a : Reformulated.AutPerF.AinfInv l (OC l)) :
    Reformulated.AutPerF.AinfInv.map l ((e l).toRingHom.comp (gOC l g)) a =
      galAway (Formalism.Per6.toBot g) (Reformulated.AutPerF.AinfInv.map l (e l).toRingHom a) := by
  refine RingHom.congr_fun (Reformulated.AutPerF.AinfInv.hom_ext
    (f := Reformulated.AutPerF.AinfInv.map l ((e l).toRingHom.comp (gOC l g)))
    (g := (galAway (Formalism.Per6.toBot g)).comp (Reformulated.AutPerF.AinfInv.map l (e l).toRingHom))
    fun w => ?_) a
  rw [RingHom.comp_apply, Reformulated.AutPerF.AinfInv.map_algebraMap, Reformulated.AutPerF.AinfInv.map_algebraMap,
    galAway_algebraMap, ← Reformulated.AutPerF.Ainf.map_map, ainfMap_eq, ainfMap_gOC]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem comparison_map_galois (g : GQ l) (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    cP l (Reformulated.AutPerF.BdRPlus.map l (gOC l g) y) = Formalism.Per6.toBot g • cP l y := by
  rw [gal_smul_bdR_def]
  refine IsPerfectoidField.evalB_ext (K := ℂ_[l]) (p := l) fun n => ?_
  rw [evalB_galBdRHom]
  change Reformulated.AutPerF.BdRPlus.eval l (NC l) n (Reformulated.AutPerF.BdRPlus.map l (e l).toRingHom
      (Reformulated.AutPerF.BdRPlus.map l (gOC l g) y)) = galQuot (Formalism.Per6.toBot g) n
      (Reformulated.AutPerF.BdRPlus.eval l (NC l) n (Reformulated.AutPerF.BdRPlus.map l (e l).toRingHom y))
  rw [Reformulated.AutPerF.BdRPlus.map_map, Reformulated.AutPerF.BdRPlus.eval_map, Reformulated.AutPerF.BdRPlus.eval_map]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Reformulated.AutPerF.BdRPlus.eval l (OC l) n y)
  rw [← ha, Ideal.quotientMap_mk, Ideal.quotientMap_mk, ainfInv_map_gOC]
  erw [galQuot_mk]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cPoint_smul (g : GQ l) (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    cP l (g • y) = Formalism.Per6.toBot g • cP l y :=
  comparison_map_galois l g y

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cD_gal (g : GQ l) (x : Reformulated.AutPerF.BdR l (OC l)) :
    cD l (g • x) = Formalism.Per6.σD g (cD l x) := by
  have key : (cD l).toRingHom.comp (MulSemiringAction.toRingHom (GQ l) (Reformulated.AutPerF.BdR l (OC l)) g) =
      (Formalism.Per6.σD g).toRingHom.comp (cD l).toRingHom := by
    refine Reformulated.AutPerF.BdR.hom_ext fun y => ?_
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      MulSemiringAction.toRingHom_apply]
    rw [Reformulated.AutPerF.BdR.smul_algebraMap, cD_algebraMap, cD_algebraMap,
      PositivityTheory.LocInh.GaloisCommutant.σD_algebraMap]
    exact congrArg (algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)) (cPoint_smul l g y)
  exact RingHom.congr_fun key x

end Cmp6
