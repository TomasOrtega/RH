import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.UnitriangularFrameLift
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdScal
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdUnit
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdRoot

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Unfold `StandingNumericalData at h`. Simplify using `only at h`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h14⟩` from `h`. Conclude with `h14 u`.
-/
theorem data_T_ne_g {C0 : ℝ} (h : StandingNumericalData D C0) (u : D.what₂.Word) :
    (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1 := by
  unfold StandingNumericalData at h
  dsimp only at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h14⟩ := h
  exact h14 u

/- English proof (translation)
The claim follows from `cIdFlag_of_steps id_scal id_unit id_cong id_root id_over X hL hTg`.
-/
theorem cIdFlag_of_lift (X : TermTie D) (hL : UnitriangularFrameLift D)
    (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1) : UnitaryVolumeMass.cIdFlag D X :=
  cIdFlag_of_steps id_scal id_unit id_cong id_root id_over X hL hTg

end Formalism.MainNotions.BridgeLemma

end
