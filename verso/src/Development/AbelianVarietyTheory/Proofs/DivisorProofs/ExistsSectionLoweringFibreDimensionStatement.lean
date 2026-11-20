import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLoweringFibreDimension
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSectionLoweringFibreDimension.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.exists_section_lowering_fibre_dimension : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (d : ℕ) (Z : Set X), IsClosed Z → (∀ ℓ : ℕ, topologicalKrullDim ↥(Z ∩ fib X ℓ) ≤ d) → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, ∀ ℓ : ℕ, topologicalKrullDim ↥((Z \ NV P e 0 f) ∩ fib X ℓ) < d := by
  first | exact @GlobalTheory.HSAmp.exists_sec_fibre_dim_lt | exact GlobalTheory.HSAmp.exists_sec_fibre_dim_lt | (intros; apply GlobalTheory.HSAmp.exists_sec_fibre_dim_lt <;> assumption)
