import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVt

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

variable {D : D7} {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)]
  [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wq x)]

/- English proof (translation)
Introduce `p hp`. Establish `hL : Formalism.L2.S.IsPtL (Formalism.L2.SG.DataInst.signPt D.R.rS p) (D.R.rS + 1)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show Formalism.L2.SG.DataInst.signPt D.R.rS p = Formalism.L2.SG.DataInst.signAux D.R.rS 1 p from rfl, Formalism.L2.SG.DataInst.sign_list_fst]`. Use `hp.1` as an intermediate fact.

Unfold `Formalism.FourierDecayAlt.TB.level at this`. Rewrite using `[this, hr]`. Use `(Formalism.L2.SG.DataInst.sign_list_mem_nonzero D.R.rS 1 p).2 fun c hc => ?_` and prove the remaining obligations. Take `⟨k, hk, rfl⟩` from `List.mem_iff_getElem.mp hc`. Conclude with `hp.2 k hk`.

Use `⟨(Formalism.L2.S.ptEquiv D.host.E (D.R.rS + 1)).symm ⟨Formalism.L2.SG.DataInst.signPt D.R.rS p, hL⟩, ?_⟩` and prove the remaining obligations. Unfold `Formalism.L2.SG.RealObj.ptOfL Formalism.L2.SG.DataInst.ptOfList`. Rewrite using `[dif_pos hL]`.
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
