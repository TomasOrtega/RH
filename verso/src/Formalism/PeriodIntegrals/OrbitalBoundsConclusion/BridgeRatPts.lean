import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalPointsComparison.BridgeApplyEqOfComp

/- English proof (translation)
The claim follows from `Formalism.L2.SG.AdBridge.adBridgeGF_main`.
-/
theorem adelic_rational_points : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeGF I :=
  Formalism.L2.SG.AdBridge.adBridgeGF_main
