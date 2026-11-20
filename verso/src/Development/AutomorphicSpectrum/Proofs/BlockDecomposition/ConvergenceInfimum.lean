import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.ConvInfProof

/- English proof (translation)
Proceed by induction on `m₀ using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Simplify using `only [Multiset.map_cons, Multiset.prod_cons]`. Conclude with `(tendsto_const_nhds.add (h.const_add a)).mul ih`.
-/
theorem tendsto_prod_shift (m₀ : Multiset ℂ) {z : ℕ → ℂ} {z₀ : ℂ} (h : Tendsto z atTop (𝓝 z₀)) (u : ℂ) :
    Tendsto (fun k => ((m₀.map (· + z k)).map (u + ·)).prod) atTop
      (𝓝 (((m₀.map (· + z₀)).map (u + ·)).prod)) := by
  induction m₀ using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (tendsto_const_nhds.add (h.const_add a)).mul ih

/- English proof (translation)
Introduce `hD hT E _ _ _ N t s τ hc hs`. Proceed by induction on `hc with`. Consider the case `leaf V z z₀ h`. Establish `hex : ∃ m₀, HasInfCharGL V τ m₀`. Break down `hs with ⟨rfl, rfl, -⟩ | ⟨-, hV, -⟩` into its components or cases.

Conclude with `⟨0, hT E τ⟩`. Conclude with `hD E _ V hV τ`. Take `⟨m₀, h₀⟩` from `hex`. Conclude with `⟨m₀.map (· + z₀), fun k => m₀.map (· + z k), ⟨m₀, h₀, rfl⟩, fun k => ⟨m₀, h₀, rfl⟩, fun u => tendsto_prod_shift m₀ h u⟩`. Consider the case `node h₁ h₂ ih₁ ih₂`.

Take `⟨a₀, a, ha₀, ha, hat⟩` from `ih₁ hs.1`. Take `⟨b₀, b, hb₀, hb, hbt⟩` from `ih₂ hs.2`. Use `⟨a₀ + b₀, fun k => a k + b k, ⟨a₀, b₀, ha₀, hb₀, rfl⟩, fun k => ⟨a k, b k, ha k, hb k, rfl⟩, fun u => ?_⟩` and prove the remaining obligations. Simplify using `only [Multiset.map_add, Multiset.prod_add]`. Conclude with `(hat u).mul (hbt u)`.
-/
theorem convInf_of_discInf_topInf : DiscInf → TopInf → ConvInf := by
  intro hD hT E _ _ _ N t s τ hc hs
  induction hc with
  | leaf V z z₀ h =>
    have hex : ∃ m₀, HasInfCharGL V τ m₀ := by
      rcases hs with ⟨rfl, rfl, -⟩ | ⟨-, hV, -⟩
      · exact ⟨0, hT E τ⟩
      · exact hD E _ V hV τ
    obtain ⟨m₀, h₀⟩ := hex
    exact ⟨m₀.map (· + z₀), fun k => m₀.map (· + z k), ⟨m₀, h₀, rfl⟩, fun k => ⟨m₀, h₀, rfl⟩,
      fun u => tendsto_prod_shift m₀ h u⟩
  | node h₁ h₂ ih₁ ih₂ =>
    obtain ⟨a₀, a, ha₀, ha, hat⟩ := ih₁ hs.1
    obtain ⟨b₀, b, hb₀, hb, hbt⟩ := ih₂ hs.2
    refine ⟨a₀ + b₀, fun k => a k + b k, ⟨a₀, b₀, ha₀, hb₀, rfl⟩,
      fun k => ⟨a k, b k, ha k, hb k, rfl⟩, fun u => ?_⟩
    simp only [Multiset.map_add, Multiset.prod_add]
    exact (hat u).mul (hbt u)

end GlobalTheory.CompanionTheory.EGlue.ConvInfProof

end
