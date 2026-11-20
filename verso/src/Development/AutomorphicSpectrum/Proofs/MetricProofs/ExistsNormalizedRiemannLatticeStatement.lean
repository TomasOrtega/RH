import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNormalizedRiemannLattice
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat.coord_lat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FExistsNormalizedRiemannLattice.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.exists_normalized_riemann_lattice : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (c : Ix Ψ j j' → Fin g → ℂ), (∀ i, c i ∈ eigSp R₀.B (emb σ i)) → (∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0) → ∃ R₁ : RiemLat E g Λ, R₁.form = R₀.form ∧ R₁.Hm = 1 ∧ ∀ a x k, R₁.B a x k = emb σ (e.symm k) a * x k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat.coord_lat | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat.coord_lat | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat.coord_lat <;> assumption)
