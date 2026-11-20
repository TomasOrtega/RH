import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalBudgetsTwoPointInductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparateTwoPointsNefBigStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

/- English proof (translation)
Introduce `hP hV hN X _ _ _ p n hproj hdim M Δ m G r N₀ x₁ x₂ c hM hΔ hklt hm hG hr hnef hbig hC h₁ h₂ hx hc hZ hs`. Use `letI := algebraΓOfHom p`. Take `⟨h, hpos, hsum, hh⟩` from `GlobalTheory.T.exists_rational_budgets_twoPointInduction n r c hr hc hs`. Establish `hr' : (0 : ℚ) < (r : ℚ)` using `by exact_mod_cast hr`. Use `GlobalTheory.T.separate_two_points_nef_big hP hV hN X p n hproj hdim M Δ m G N₀ (1 / (r : ℚ)) h x₁ x₂ hM hΔ hklt hm hG hnef hbig ?_ h₁ h₂ hx hpos ?_ hsum (by positivity)` and prove the remaining obligations.

Introduce `C hCc`. Rewrite using `[hC C hCc]`. Expand and normalize the polynomial expressions, which then agree. Introduce `z e hz he hze`. Establish `hle : e ≤ n`.

Establish `h1` using `topologicalKrullDim_subspace_le X (closure ({z} : Set X))`. Rewrite `h1` using `[hze, hdim]`. Conclude with `h1` after adjusting the coercions. Establish `hmem : x₁ ∈ Closeds.closure ({z} : Set X) ∨ x₂ ∈ Closeds.closure ({z} : Set X)`. Break down `hz with hz | hz` into its components or cases.

Conclude with `Or.inl (specializes_iff_mem_closure.1 hz)`. Conclude with `Or.inr (specializes_iff_mem_closure.1 hz)`. Establish `hZ'` using `hZ (Closeds.closure ({z} : Set X)) e isIrreducible_singleton.closure hmem he hze`. Conclude with `hh e (Finset.mem_Icc.2 ⟨he, hle⟩) _ hZ'`.
-/
theorem pointSeparationPair_of_vanishing :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics →
      GlobalTheory.Published.PointSeparationPair := by
  intro hP hV hN X _ _ _ p n hproj hdim M Δ m G r N₀ x₁ x₂ c hM hΔ hklt hm hG hr hnef hbig hC
    h₁ h₂ hx hc hZ hs
  letI := algebraΓOfHom p
  obtain ⟨h, hpos, hsum, hh⟩ := GlobalTheory.T.exists_rational_budgets_twoPointInduction n r c hr hc hs
  have hr' : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr
  refine GlobalTheory.T.separate_two_points_nef_big hP hV hN X p n hproj hdim M Δ m G N₀ (1 / (r : ℚ)) h x₁ x₂ hM hΔ hklt hm hG
    hnef hbig ?_ h₁ h₂ hx hpos ?_ hsum (by positivity)
  · intro C hCc
    rw [hC C hCc]
    ring
  · intro z e hz he hze
    have hle : e ≤ n := by
      have h1 := topologicalKrullDim_subspace_le X (closure ({z} : Set X))
      rw [hze, hdim] at h1
      exact_mod_cast h1
    have hmem : x₁ ∈ Closeds.closure ({z} : Set X) ∨ x₂ ∈ Closeds.closure ({z} : Set X) := by
      rcases hz with hz | hz
      · exact Or.inl (specializes_iff_mem_closure.1 hz)
      · exact Or.inr (specializes_iff_mem_closure.1 hz)
    have hZ' := hZ (Closeds.closure ({z} : Set X)) e isIrreducible_singleton.closure hmem he hze
    exact hh e (Finset.mem_Icc.2 ⟨he, hle⟩) _ hZ'

end GlobalTheory
