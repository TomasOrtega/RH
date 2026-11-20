import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusMonomialMemRange
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GeoTpow.tpow_mem_range` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTorusMonomialMemRange.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.torus_monomial_mem_range : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), 0 < e → ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)) (ht : ∀ k, IsUnit (tV i y hy V hV k)), ∀ m ∈ expS S, tpow (fun k => (ht k).unit) m ∈ Set.range (evV i (yS y S) V hS) := by
  first | exact @GlobalTheory.CompanionTheory.GeoTpow.tpow_mem_range | exact GlobalTheory.CompanionTheory.GeoTpow.tpow_mem_range | (intros; apply GlobalTheory.CompanionTheory.GeoTpow.tpow_mem_range <;> assumption)
