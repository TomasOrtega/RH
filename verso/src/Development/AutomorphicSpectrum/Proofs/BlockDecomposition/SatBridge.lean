import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SatBridge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSatakeOfIsSatVecGL

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LFun

namespace GlobalTheory.CompanionTheory.SatakeBridge

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem satBridge : PositivityTheory.SphericalProduct.SatBridge := by
  intro E _ _ w n V _ _ ρ hs hi α
  constructor
  · exact GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake E w n V ρ α
  · intro h
    obtain ⟨x, hx⟩ := h.exists_vec
    exact GlobalTheory.CompanionTheory.SatComp.hasSatake_of_isSatVecGL ⟨hs, hi⟩ α hx

end GlobalTheory.CompanionTheory.SatakeBridge

end
