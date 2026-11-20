import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionDepthHostFixingAutInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolFan.isTwInv_starDepth` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FStarSubdivisionDepthHostFixingAutInvariant.lean&line=123#L123)
-/
theorem _root_.GlobalTheory.T.starSubdivisionDepth_hostFixingAut_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ w : InvFun (𝓞 E)), IsTwInv H ψ → IsTwInv H w → IsTwInv H (starDepth H.bar ψ w) := by
  first | exact @GlobalTheory.PolFan.isTwInv_starDepth | exact GlobalTheory.PolFan.isTwInv_starDepth | (intros; apply GlobalTheory.PolFan.isTwInv_starDepth <;> assumption)
