import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersAutCommHostConjugation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ringOfIntegers_equiv_bar_comm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FRingOfIntegersAutCommHostConjugation.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.ringOfIntegers_aut_comm_hostConjugation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E), τ (H.bar a) = H.bar (τ a) := by
  first | exact @GlobalTheory.ringOfIntegers_equiv_bar_comm | exact GlobalTheory.ringOfIntegers_equiv_bar_comm | (intros; apply GlobalTheory.ringOfIntegers_equiv_bar_comm <;> assumption)
