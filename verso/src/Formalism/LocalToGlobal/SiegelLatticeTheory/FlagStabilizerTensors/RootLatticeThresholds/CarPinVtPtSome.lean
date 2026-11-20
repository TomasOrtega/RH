import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVt

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

variable {D : D7} {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)]
  [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wq x)]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ptSome_of (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (hr : S.G.r = D.R.rS) : PtSome S := by
  intro p hp
  have hL : Formalism.L2.S.IsPtL (Formalism.L2.SG.DataInst.signPt D.R.rS p) (D.R.rS + 1) := by
    refine ⟨?_, ?_⟩
    · rw [show Formalism.L2.SG.DataInst.signPt D.R.rS p = Formalism.L2.SG.DataInst.signAux D.R.rS 1 p from rfl,
        Formalism.L2.SG.DataInst.sign_list_fst]
      have := hp.1
      unfold Formalism.FourierDecayAlt.TB.level at this
      rw [this, hr]
    · refine (Formalism.L2.SG.DataInst.sign_list_mem_nonzero D.R.rS 1 p).2 fun c hc => ?_
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hc
      exact hp.2 k hk
  refine ⟨(Formalism.L2.S.ptEquiv D.host.E (D.R.rS + 1)).symm ⟨Formalism.L2.SG.DataInst.signPt D.R.rS p, hL⟩, ?_⟩
  unfold Formalism.L2.SG.RealObj.ptOfL Formalism.L2.SG.DataInst.ptOfList
  rw [dif_pos hL]

end Formalism.L2.SG.Pf.Carrier.CarPinVt
