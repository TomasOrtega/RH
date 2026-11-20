import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
open Formalism.BasicNotions GlobalTheory.Mem.HD

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem GlobalTheory.Mem.HD.levelTied_of_levEx : ∀ D : D7, LevEx D → Formalism.L2.Host.LevelTied D :=
  fun D h => ⟨fun p => by
    have hq : Formalism.MainNotions.q0Av D = Formalism.MainNotions.AbsolutelyIrreducibleSpan.q0 D := rfl
    simpa [hq] using h p⟩
