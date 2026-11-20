import Mathlib
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelOperatorMapsStabiliserEquivariantFormsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassSumTermLawStabiliserTargetStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerTieEntire
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberFormsStableOfReferenceTuple

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.KerJ Classical

namespace GlobalTheory.KFiClose

/- English proof (translation)
Introduce `D L hT Gi Gl K Y cX ex t hC hF`. Establish `second : ∀ u μ, DV.Used D μ → ∀ i < D.R.m, ∀ φ ∈ (ex.tw.fm u μ).Fi i, (D.chTw u μ).K i φ ∈ (ex.tw.fm u μ).Fi (i + 1)`. Introduce `u μ hμ`. Take `⟨G, hFA, hSP⟩` from `hF u μ hμ`. Conclude with `GlobalTheory.T.kernelOperator_maps_stabiliserEquivariant_forms D u (D.chTw u μ) _ _ (ex.tw.fm u μ) (t.O u μ) G hFA (t.unf u μ) (fun i hi c c' => GlobalTheory.KerTieEntire.kerTie_entire D L hT Gi Gl K Y cX ex t u μ i hi c c') (GlobalTheory.T.classSum_term_law_stabiliser_target D L …`.

Establish `h0 : DV.Used D D.what₂.mu0`. Unfold `DV.Used`. Conclude with `Or.inl rfl`. Conclude with `⟨fun u i hi => GlobalTheory.KFiMu0.memberForms_stable_of_reference_tuple D ex.tw u i hi (second u _ h0 i hi), second⟩`.
-/
theorem kFi_of_tie : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → FormsPin t → OrbitPlaces.KFi D ex.tw := by
  intro D L hT Gi Gl K Y cX ex t hC hF
  have second : ∀ u μ, DV.Used D μ → ∀ i < D.R.m, ∀ φ ∈ (ex.tw.fm u μ).Fi i, (D.chTw u μ).K i φ ∈ (ex.tw.fm u μ).Fi (i + 1) := by
    intro u μ hμ
    obtain ⟨G, hFA, hSP⟩ := hF u μ hμ
    exact GlobalTheory.T.kernelOperator_maps_stabiliserEquivariant_forms D u (D.chTw u μ) _ _ (ex.tw.fm u μ) (t.O u μ) G hFA (t.unf u μ)
      (fun i hi c c' => GlobalTheory.KerTieEntire.kerTie_entire D L hT Gi Gl K Y cX ex t u μ i hi c c')
      (GlobalTheory.T.classSum_term_law_stabiliser_target D L hT Gi Gl K Y cX ex t hC u μ G hSP)
  have h0 : DV.Used D D.what₂.mu0 := by
    unfold DV.Used
    exact Or.inl rfl
  exact ⟨fun u i hi => GlobalTheory.KFiMu0.memberForms_stable_of_reference_tuple D ex.tw u i hi (second u _ h0 i hi), second⟩

end GlobalTheory.KFiClose
