import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem exists_hSpace_sigOK_sig :
    ∀ (D : D7) (P Q : ℕ), ∃ U : HSpace D.host.E, U.SigOK ∧ ∀ τ, U.sig τ = (P, Q) := by
  intro D P Q
  refine ⟨bandSpace D (P + Q) P (P + Q), bandSpace_sigOK D (P + Q) P (P + Q) le_rfl, fun τ => ?_⟩
  show (P + Q - (P + Q - P), P + Q - P) = (P, Q)
  congr 1 <;> omega

end GlobalTheory
