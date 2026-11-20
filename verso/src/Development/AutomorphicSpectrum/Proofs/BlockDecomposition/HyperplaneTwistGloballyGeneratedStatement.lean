import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperplaneTwistGloballyGenerated
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHyperplaneTwistGloballyGenerated.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.hyperplane_twist_globally_generated : ∀ (Y : Var ℂ) (i : Fin (Y.N + 1)) (hi : Y.ι (genericPoint Y.X) ∈ ProjSpace.chart ℂ Y.N i) (Δ : Y.Dv), ∀ᶠ m : ℕ in Filter.atTop, ∃ (L : LB Y.X) (r : L.ι → Y.Fnˣ) (n : ℕ) (b : Fin n → L.Sec), L.IsLB ∧ Presents (Δ + m • Y.hyp hi) L r ∧ ⨆ j, nonzeroLocus (b j) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SerreBpf.eventually_basePointFree | exact GlobalTheory.CompanionTheory.SerreBpf.eventually_basePointFree | (intros; apply GlobalTheory.CompanionTheory.SerreBpf.eventually_basePointFree <;> assumption)
