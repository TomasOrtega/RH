import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsRationalFunctionsLociStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

/- English proof (translation)
Introduce `k _ X _ p D _ P hA S hS`. Take `⟨n, hn, s, h₁, -, -⟩` from `hA.exists_affine_finite_subset hS (U := ⊤) (Set.subset_univ _)`. Take `⟨f, hf, e⟩` from `(GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci k X p P n).1 s`. Use `⟨n, hn, f, hf, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`.

Conclude with `h₁`.
-/
theorem exists_sec_nonvanishing_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ S : Set X, S.Finite → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, S ⊆ NV P e 0 f := by
  intro k _ X _ p D _ P hA S hS
  obtain ⟨n, hn, s, h₁, -, -⟩ := hA.exists_affine_finite_subset hS (U := ⊤) (Set.subset_univ _)
  obtain ⟨f, hf, e⟩ := (GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci k X p P n).1 s
  refine ⟨n, hn, f, hf, ?_⟩
  rw [e]
  exact h₁

end GlobalTheory.HSAmp
