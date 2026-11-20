import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionDegreeSlopeBound
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorusSlope.slope_le_of_torusExt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorusExtensionDegreeSlopeBound.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.torus_extension_degree_slope_bound : ∀ (m : ℕ) (C : ℝ), 1 ≤ C → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (K : Type) [Field K] [NumberField K] (r m' : ℕ) (h : HermFam K (Fin m → K)) (L : Submodule (𝓞 K) (Fin m → K)) (ε : Fin r → Fin m → K) (q : (Fin m → K) →ₗ[K] (Fin m' → K)) (h' : HermFam K (Fin m' → K)) (L' : Submodule (𝓞 K) (Fin m' → K)), TorusExt h L ε q h' L' C → -deg h' L' ≤ -deg h L + C' ∧ ∀ ν : ℝ, 0 ≤ ν → MuLe h' L' ν → MuLe h L (ν + C') := by
  first | exact @GlobalTheory.TorusSlope.slope_le_of_torusExt | exact GlobalTheory.TorusSlope.slope_le_of_torusExt | (intros; apply GlobalTheory.TorusSlope.slope_le_of_torusExt <;> assumption)
