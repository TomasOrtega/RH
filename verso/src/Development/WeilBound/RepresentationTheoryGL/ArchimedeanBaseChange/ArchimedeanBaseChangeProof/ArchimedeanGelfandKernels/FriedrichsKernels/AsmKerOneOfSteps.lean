import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps

namespace PositivityTheory.RgBcC.Fc

open PositivityTheory.RgBcC

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem asmKerOne_of_steps (hC : AsmCpt) (hS : CalcSteps) (hO : SmoothOp) (hP : PWdecay) (hK : KerCore)
    (hL : KerLoc) (hW : KerW) : AsmKerOne := by
  intro h1 h2 h3 h4 h5 h6 n _ _ μ _ E w g T hg
  have hWC : WaveCpt := hC h1 h2 h3 h4
  apply hW n μ E w g h1 h2 h3
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hK n μ E g T hg h1 h2 h3 h4 h5 h6 hWC hS hO hP
  exact ⟨k, hL n μ E g T k hg h1 h2 h3 h6 hWC hk1 hk2 hk3 hk4⟩

end PositivityTheory.RgBcC.Fc
