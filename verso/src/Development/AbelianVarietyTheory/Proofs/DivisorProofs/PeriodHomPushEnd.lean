import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPeriodsNaturalAlongCoveredMorphismStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

/- English proof (translation)
Introduce `A _ g hA L u P hP α _ M hM x x' hx`. Establish `hsep : A.left.IsSeparated` using `by haveI : IsProper A.hom := hA.proper`. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[← terminal.comp_from A.hom]`. Use `infer_instance`.

Establish `hΛ : ∀ l : u.Λ, M l ∈ u.Λ` using `fun l ↦ by`. Rewrite using `[← u.ker, hM, (u.ker _).2 l.2, MonObj.one_comp]`. Set `N : u.Λ →+ u.Λ` to `{ toFun l := ⟨M l, hΛ l⟩ map_zero' := Subtype.ext (map_zero M) map_add' a b := Subtype.ext (map_add M _ _) }`. Take `rfl : x' = N x` from `Subtype.ext hx`. Use `LinearMap.ext fun c ↦ ?_` and prove the remaining obligations.

Establish `key` using `GlobalTheory.T.holomorphicPeriods_natural_along_covered_morphism (fibUnif u) (fibUnif u) hsep hsep id analyticOnNhd_id (fun _ h ↦ h) M N (fun _ _ _ ↦ rfl) (RingHom.id ℂ) α.left (homMor (dp0 ℂ) (𝟙 _) α).isMor (fun _ ↦ rfl) (fun p _ ↦ (congrArg Over.Hom.left (hM p.2)).symm) c.1 _ _ …`. Conclude with `congrArg (fun f : Hol (fibFam u).V ↦ f.1 ⟨0, trivial⟩) key`.
-/
theorem periodHom_push_end : PEnd := by
  intro A _ g hA L u P hP α _ M hM x x' hx
  have hsep : A.left.IsSeparated := by
    haveI : IsProper A.hom := hA.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from A.hom]
    infer_instance
  have hΛ : ∀ l : u.Λ, M l ∈ u.Λ := fun l ↦ by
    rw [← u.ker, hM, (u.ker _).2 l.2, MonObj.one_comp]
  let N : u.Λ →+ u.Λ :=
    { toFun l := ⟨M l, hΛ l⟩
      map_zero' := Subtype.ext (map_zero M)
      map_add' a b := Subtype.ext (map_add M _ _) }
  obtain rfl : x' = N x := Subtype.ext hx
  refine LinearMap.ext fun c ↦ ?_
  have key := GlobalTheory.T.holomorphicPeriods_natural_along_covered_morphism (fibUnif u) (fibUnif u) hsep hsep id analyticOnNhd_id (fun _ h ↦ h) M N
    (fun _ _ _ ↦ rfl) (RingHom.id ℂ) α.left (homMor (dp0 ℂ) (𝟙 _) α).isMor (fun _ ↦ rfl)
    (fun p _ ↦ (congrArg Over.Hom.left (hM p.2)).symm) c.1 _ _ (hP c)
    (hP (primPull (dp0 ℂ) (𝟙 _) α c)) x
  exact congrArg (fun f : Hol (fibFam u).V ↦ f.1 ⟨0, trivial⟩) key

end GlobalTheory.AnPer
