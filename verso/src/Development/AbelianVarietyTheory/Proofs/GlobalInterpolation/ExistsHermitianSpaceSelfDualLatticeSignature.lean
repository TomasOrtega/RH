import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Introduce `D P Q`. Use `⟨bandSpace D (P + Q) P (P + Q), bandSpace_sigOK D (P + Q) P (P + Q) le_rfl, fun τ => ?_⟩` and prove the remaining obligations. Use `show (P + Q - (P + Q - P), P + Q - P) = (P, Q)`. Apply the tactic sequence `congr 1 <;> omega`.
-/
theorem exists_hSpace_sigOK_sig :
    ∀ (D : D7) (P Q : ℕ), ∃ U : HSpace D.host.E, U.SigOK ∧ ∀ τ, U.sig τ = (P, Q) := by
  intro D P Q
  refine ⟨bandSpace D (P + Q) P (P + Q), bandSpace_sigOK D (P + Q) P (P + Q) le_rfl, fun τ => ?_⟩
  show (P + Q - (P + Q - P), P + Q - P) = (P, Q)
  congr 1 <;> omega

end GlobalTheory
