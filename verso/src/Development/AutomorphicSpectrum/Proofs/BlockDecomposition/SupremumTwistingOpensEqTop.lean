import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeCover

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Introduce `R _ X D N i h`. Take `⟨-, s, hs, -⟩` from `h`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨j, hj⟩` from `GlobalTheory.ProjSpace.exists_mem_chart R N (i x)`.

Use `haveI : IsOpenImmersion (chart R N j) := by`. Unfold `chart`. Use `infer_instance`. Establish `hmem : (pullback.fst i (chart R N j)).opensRange ∈ 𝒱D D` using `⟨(pullback.fst i (chart R N j)).isoOpensRange.inv ≫ s j, by`. Rewrite using `[Category.assoc, hs, Scheme.Hom.isoOpensRange_inv_comp]⟩`.

Use `TopologicalSpace.Opens.mem_sSup.2 ⟨_, hmem, ?_⟩` and prove the remaining obligations. Establish `e : (chart R N j).opensRange = GlobalTheory.ProjSpace.chart R N j` using `Proj.opensRange_awayι _ _ _ _`. Establish `hr : i x ∈ ((chart R N j).opensRange : Set _)`. Rewrite using `[e]`. Conclude with `hj`.

Rewrite `hr` using `[Scheme.Hom.coe_opensRange]`. Use `show x ∈ ((pullback.fst i (chart R N j)).opensRange : Set X)`. Rewrite using `[Scheme.Hom.coe_opensRange, Scheme.Pullback.range_fst]`. Conclude with `hr`.
-/
theorem main : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ)
    (i : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace R N), IsTautologicalLineAt D N i → sSup (𝒱D D) = ⊤ := by
  intro R _ X D N i h
  obtain ⟨-, s, hs, -⟩ := h
  rw [eq_top_iff]
  intro x _
  obtain ⟨j, hj⟩ := GlobalTheory.ProjSpace.exists_mem_chart R N (i x)
  haveI : IsOpenImmersion (chart R N j) := by
    unfold chart
    infer_instance
  have hmem : (pullback.fst i (chart R N j)).opensRange ∈ 𝒱D D :=
    ⟨(pullback.fst i (chart R N j)).isoOpensRange.inv ≫ s j, by
      rw [Category.assoc, hs, Scheme.Hom.isoOpensRange_inv_comp]⟩
  refine TopologicalSpace.Opens.mem_sSup.2 ⟨_, hmem, ?_⟩
  have e : (chart R N j).opensRange = GlobalTheory.ProjSpace.chart R N j := Proj.opensRange_awayι _ _ _ _
  have hr : i x ∈ ((chart R N j).opensRange : Set _) := by
    rw [e]
    exact hj
  rw [Scheme.Hom.coe_opensRange] at hr
  show x ∈ ((pullback.fst i (chart R N j)).opensRange : Set X)
  rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_fst]
  exact hr

end GlobalTheory.CompanionTheory.ConeCover
