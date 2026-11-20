import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantCarrierDimPolyFan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsInvariantCarrierDimPolyFan.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.exists_invariant_carrierDim_polyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → ∃ lab : InvFun (𝓞 E), IsTwInv H lab ∧ IsCarrierDim H.bar q ψ lab := by
  first | exact @GlobalTheory.PolFan.CarDim.exists_isCarrierDim | exact GlobalTheory.PolFan.CarDim.exists_isCarrierDim | (intros; apply GlobalTheory.PolFan.CarDim.exists_isCarrierDim <;> assumption)
