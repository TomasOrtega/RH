import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AeZeroCountEqIntersection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAeZeroCountEqIntersection.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.ae_zero_count_eq_intersection : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → ∀ᵐ C ∂(volume : Measure (Fin Y.dim → Fin n → ℂ)), ((({y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}).ncard : ℕ) : ℤ) = Y.inter fun _ => Δ := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.koszul_count | exact GlobalTheory.CompanionTheory.KoszulCount.koszul_count | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.koszul_count <;> assumption)
