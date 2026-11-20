import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedFDerivAlgebraicDirectionsJetTransport
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FIteratedFDerivAlgebraicDirectionsJetTransport.lean&line=176#L176)
-/
theorem _root_.GlobalTheory.T.iteratedFDeriv_algebraic_directions_jet_transport : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (G : VC D N N' → ℂ), ContDiff ℂ ⊤ G → CoefIn D G Qbar → ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E), iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) ∈ Qbar ∧ jet D lam y (pSer D lam G) = lamC lam (iteratedFDeriv ℂ m G 0 fun j => embV D (tor0 D cc δ) (y j)) := by
  first | exact @GlobalTheory.JetTransport.jet_pSer | exact GlobalTheory.JetTransport.jet_pSer | (intros; apply GlobalTheory.JetTransport.jet_pSer <;> assumption)
