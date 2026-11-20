import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.InChartIffOfDominates
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_iff_of_dominates` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FInChartIffOfDominates.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.inChart_iff_of_dominates' : ∀ (X X' : Scheme.{0}) (Ω G : Type) [Field Ω] [Field G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of G) ⟶ X') (f : X' ⟶ X) (i : Ω →+* G) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => i (x k)) c₁ p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_iff_of_dominates | exact GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_iff_of_dominates | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_iff_of_dominates <;> assumption)
