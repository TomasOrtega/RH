import Mathlib
import Development.AutomorphicArithmetic.CMTraceForms.Places
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AutomorphicArithmetic.CMTraceForms.SplitPlacesDiscriminantDepthOfSplitAt
import Development.AutomorphicArithmetic.CMTraceForms.CmDatumDiscriminantDepthBounds
import Formalism.LocalRingCardinality.HostCls
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.CharDepth

/- English proof (translation)
Introduce `D H hd p _ hp`. Establish `hpp : p.Prime` using `Fact.out`. Establish `hs : UpperTheory.Depth.SplitAt H.d p`. Distinguish the cases in `h2 : p = 2`. Conclude with `Or.inl h2`.

Conclude with `Or.inr (by rw [hd]; exact D.host.QS_split p hpp h2 (D.host.mem_small_iff.1 hp).2)`. Take `⟨h1, -, -, -, h5⟩` from `UpperTheory.cmDatum_discriminantDepth_bounds D.host.toHostAx`. Use `⟨hs, ?_, D.host.vdH_nonneg p, (h1 p hp).1.trans (h1 p hp).2⟩` and prove the remaining obligations. Rewrite using `[h5 p]`. Conclude with `UpperTheory.splitPlaces_discriminantDepth_of_splitAt p D.host.E H hs D.R.f D.host.finrank_E'`.
-/
theorem twoPlaces_host : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E), H.d = D.host.d → ∀ (p : ℕ) [Fact p.Prime], p ∈ D.host.small → UpperTheory.Depth.SplitAt H.d p ∧ UpperTheory.Depth.SplitPlaces p H D.R.f (D.host.vdH p) ∧ 0 ≤ D.host.vdH p ∧ D.host.vdH p ≤ vd2 D := by
  intro D H hd p _ hp
  have hpp : p.Prime := Fact.out
  have hs : UpperTheory.Depth.SplitAt H.d p := by
    by_cases h2 : p = 2
    · exact Or.inl h2
    · exact Or.inr (by rw [hd]; exact D.host.QS_split p hpp h2 (D.host.mem_small_iff.1 hp).2)
  obtain ⟨h1, -, -, -, h5⟩ := UpperTheory.cmDatum_discriminantDepth_bounds D.host.toHostAx
  refine ⟨hs, ?_, D.host.vdH_nonneg p, (h1 p hp).1.trans (h1 p hp).2⟩
  rw [h5 p]
  exact UpperTheory.splitPlaces_discriminantDepth_of_splitAt p D.host.E H hs D.R.f D.host.finrank_E'

end GlobalTheory.CharDepth
