import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionSubordinateToFan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FStarSubdivisionSubordinateToFan.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.starSubdivision_subordinate_to_fan : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ w ψ' : InvFun O), IsStarOf bar q ψ w ψ' → Subordinate bar q ψ' ψ := by
  first | exact @GlobalTheory.PolFan.subordinate_of_isStarOf | exact GlobalTheory.PolFan.subordinate_of_isStarOf | (intros; apply GlobalTheory.PolFan.subordinate_of_isStarOf <;> assumption)
