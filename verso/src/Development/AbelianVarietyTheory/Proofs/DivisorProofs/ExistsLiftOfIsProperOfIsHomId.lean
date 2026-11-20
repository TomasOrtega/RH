import Mathlib
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtPointLiftOfSurjectiveLocFinType
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

namespace GlobalTheory

/- English proof (translation)
Introduce `o Ω _ _ _ Y M q hq hp p _ y`. Apply the tactic sequence `have hq' : Y.pt ≫ q = spMap (AlgHom.id o Ω).toRingHom ≫ M.pt := by first | exact hq | exact hq.1 | exact hq.2`. Establish `hsurj : Function.Surjective q`. Establish `hc : IsClosed (Set.range q)` using `q.isClosedMap.isClosed_range`. Establish `hg : genericPoint M.Z ∈ Set.range q`.

Establish `w : Sp Ω` using `IsLocalRing.closedPoint Ω`. Use `⟨Y.pt w, ?_⟩` and prove the remaining obligations. Establish `h1 : (Y.pt ≫ q) w = (spMap (AlgHom.id o Ω).toRingHom ≫ M.pt) w` using `by rw [hq']`. Rewrite `h1` using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, M.pt_apply]`. Conclude with `h1`.

Introduce `z`. Conclude with `(genericPoint_specializes z).mem_closed hc hg`. Take `⟨K', _, σ, y₁, hσ, hy₁⟩` from `exists_finite_ext_point_lift_of_surjective_lft q inferInstance hsurj (PadicAlgCl p) (gPt p ≫ y)`. Establish `hbij : Function.Bijective σ`. Use `letI := σ.toAlgebra`.

Use `haveI : Module.Finite (PadicAlgCl p) K' := hσ`. Conclude with `IsAlgClosed.algebraMap_bijective_of_isIntegral (k := PadicAlgCl p) (K := K')`. Set `e` to `RingEquiv.ofBijective σ hbij`. Establish `he : e.symm.toRingHom.comp σ = RingHom.id _` using `RingHom.ext fun x => e.symm_apply_apply x`. Establish `h2 : (spMap e.symm.toRingHom ≫ y₁) ≫ q = gPt p ≫ y`.

Rewrite using `[Category.assoc, hy₁, ← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, he]`. Establish `: spMap (RingHom.id (PadicAlgCl p)) = 𝟙 _` using `Spec.map_id _`. Rewrite using `[this, Category.id_comp]`. Establish `hE : ValuativeCriterion.Existence q` using `(UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed q) : (ValuativeCriterion.Existence ⊓ @QuasiCompact) q).1`. Take `⟨⟨l⟩⟩` from `hE { R := OO p, K := PadicAlgCl p, i₁ := spMap e.symm.toRingHom ≫ y₁, i₂ := y, commSq := ⟨h2⟩ }`.

Conclude with `⟨l.l, l.fac_right⟩`.
-/
theorem exists_lift_of_isProper_of_isHom_id :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω) (q : Y.Z ⟶ M.Z),
      M.IsHom Y (AlgHom.id o Ω) q → IsProper q → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z),
        ∃ y' : Sp (OO p) ⟶ Y.Z, y' ≫ q = y := by
  intro o Ω _ _ _ Y M q hq hp p _ y
  have hq' : Y.pt ≫ q = spMap (AlgHom.id o Ω).toRingHom ≫ M.pt := by
    first | exact hq | exact hq.1 | exact hq.2
  have hsurj : Function.Surjective q := by
    have hc : IsClosed (Set.range q) := q.isClosedMap.isClosed_range
    have hg : genericPoint M.Z ∈ Set.range q := by
      have w : Sp Ω := IsLocalRing.closedPoint Ω
      refine ⟨Y.pt w, ?_⟩
      have h1 : (Y.pt ≫ q) w = (spMap (AlgHom.id o Ω).toRingHom ≫ M.pt) w := by rw [hq']
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, M.pt_apply] at h1
      exact h1
    intro z
    exact (genericPoint_specializes z).mem_closed hc hg
  obtain ⟨K', _, σ, y₁, hσ, hy₁⟩ := exists_finite_ext_point_lift_of_surjective_lft q inferInstance hsurj
    (PadicAlgCl p) (gPt p ≫ y)
  have hbij : Function.Bijective σ := by
    letI := σ.toAlgebra
    haveI : Module.Finite (PadicAlgCl p) K' := hσ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral (k := PadicAlgCl p) (K := K')
  let e := RingEquiv.ofBijective σ hbij
  have he : e.symm.toRingHom.comp σ = RingHom.id _ := RingHom.ext fun x => e.symm_apply_apply x
  have h2 : (spMap e.symm.toRingHom ≫ y₁) ≫ q = gPt p ≫ y := by
    rw [Category.assoc, hy₁, ← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, he]
    have : spMap (RingHom.id (PadicAlgCl p)) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]
  have hE : ValuativeCriterion.Existence q :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed q) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) q).1
  obtain ⟨⟨l⟩⟩ := hE
    { R := OO p, K := PadicAlgCl p, i₁ := spMap e.symm.toRingHom ≫ y₁, i₂ := y, commSq := ⟨h2⟩ }
  exact ⟨l.l, l.fac_right⟩

end GlobalTheory
