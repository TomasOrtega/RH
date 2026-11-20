import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.PowEigAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharCMEtaLocalEqNegOnePowValInert

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `E _ _ _ μ e hμ w hw k`. Establish `h1 : μ.val w = -1` using `by show μ.loc w (GlobalTheory.Mem.Chr.atFin w (GlobalTheory.Mem.Chr.unif w)) = -1`. Rewrite using `[hμ.2.2.1 w hw, GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.ord_eq_one (GlobalTheory.MuInert.valuation_eq_uniformizer w (GlobalTheory.Mem.Chr.unif_spec w)), zpow_one]`. Proceed by induction on `k with`. Consider the case `zero => simp [HChar.val, HChar.locK, HChar.loc]`.

Consider the case `succ k ih => rw [pow_succ, pow_succ, HChar.val_mul, ih, h1]`.
-/
theorem UpperTheory.HeckeLevelFrameExistence.muVal :
    UpperTheory.HeckeLevelFrameExistence.MuVal := by
  intro E _ _ _ μ e hμ w hw k
  have h1 : μ.val w = -1 := by
    show μ.loc w (GlobalTheory.Mem.Chr.atFin w (GlobalTheory.Mem.Chr.unif w)) = -1
    rw [hμ.2.2.1 w hw, GlobalTheory.SmGL.unrChar_apply,
      GlobalTheory.SmGL.ord_eq_one (GlobalTheory.MuInert.valuation_eq_uniformizer w (GlobalTheory.Mem.Chr.unif_spec w)), zpow_one]
  induction k with
  | zero => simp [HChar.val, HChar.locK, HChar.loc]
  | succ k ih => rw [pow_succ, pow_succ, HChar.val_mul, ih, h1]
