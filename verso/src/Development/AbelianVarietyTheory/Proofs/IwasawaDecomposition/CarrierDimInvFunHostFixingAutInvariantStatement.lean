import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimInvFunHostFixingAutInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolFan.CarDim.isTwInv_carFun` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCarrierDimInvFunHostFixingAutInvariant.lean&line=227#L227)
-/
theorem _root_.GlobalTheory.T.carrierDimInvFun_hostFixingAut_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E)), IsTwInv H ψ → IsTwInv H (carFun H.bar ψ) := by
  first | exact @GlobalTheory.PolFan.CarDim.isTwInv_carFun | exact GlobalTheory.PolFan.CarDim.isTwInv_carFun | (intros; apply GlobalTheory.PolFan.CarDim.isTwInv_carFun <;> assumption)
