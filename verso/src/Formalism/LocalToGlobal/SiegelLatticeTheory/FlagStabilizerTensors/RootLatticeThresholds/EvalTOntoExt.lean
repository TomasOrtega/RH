import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransferOfFundamentalDomains

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.RowDict Formalism.MainNotions.LeviCoordinates Formalism.L2.Theta

namespace Formalism.L2.SG.EvalTOntoExt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

abbrev NN : Set X.B.I.GA := rr_N (rr_GF X.B.I) X.B.fund

open Classical in

def ext0 (f : L2X X) (y : X.B.I.GA) : ℂ :=
  if y ∈ NN X then 0 else (f : X.B.I.GA → ℂ) (rr_rep X.B.I.GFset X.B.fund y)

/- English proof (translation)
The claim follows from `rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec`.
-/
theorem hFD : rr_FD (X.B.I.muA X.B.μf) (rr_GF X.B.I) X.B.fund := rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec

/- English proof (translation)
Use `X.B.sf` as an intermediate fact. Use `X.B.haar` as an intermediate fact. Use `Formalism.L2.SG.Pf.muf_right X` as an intermediate fact. Conclude with `⟨rr_muA_sigmaFinite X.B.I X.B.μf, rr_muA_left X.B.I X.B.μf, rr_muA_right X.B.I X.B.μf⟩`.
-/
theorem instances : SigmaFinite (X.B.I.muA X.B.μf) ∧ (X.B.I.muA X.B.μf).IsMulLeftInvariant ∧
    (X.B.I.muA X.B.μf).IsMulRightInvariant := by
  have := X.B.sf
  have := X.B.haar
  have := Formalism.L2.SG.Pf.muf_right X
  exact ⟨rr_muA_sigmaFinite X.B.I X.B.μf, rr_muA_left X.B.I X.B.μf, rr_muA_right X.B.I X.B.μf⟩

end Formalism.L2.SG.EvalTOntoExt

end
