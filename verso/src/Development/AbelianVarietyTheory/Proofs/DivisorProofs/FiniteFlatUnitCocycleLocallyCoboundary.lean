import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFaithfullyFlatAlgebraOverAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSquareEquivFibreSquareSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleDescendsOnTripleOverlapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Hilbert90LocalOfCocycleTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitBasicOpenOfCoboundaryIdentityStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LBDescent

/- English proof (translation)
Introduce `X Y f _ _ _ _ V c hc y hy`. Take `⟨V₀, hV₀, hyV₀, hV₀V⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hy`. Establish `h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀` using `fun z hz => by show f (pullback.snd f f z) ∈ V₀`. Rewrite using `[← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]`. Conclude with `hz`.

Establish `hle : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V` using `fun z hz => hV₀V hz`. Use `letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra`. Take `⟨hN, hF, hFF⟩` from `GlobalTheory.T.finite_faithfullyFlat_algebra_over_affine_open f V₀ hV₀`. Take `⟨e, he⟩` from `GlobalTheory.T.exists_tensorSquare_equiv_fibreSquare_sections f V₀ hV₀ h`. Establish `hcoc` using `GlobalTheory.T.unit_cocycle_descends_on_triple_overlaps f V V₀ hV₀ h hle c hc e he`.

Set `c₀ : (Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀))ˣ` to `Units.map e.symm.toMonoidHom (res hle c)`. Take `⟨r, hr, m, s, n, hm, hs⟩` from `GlobalTheory.T.hilbert90_of_cocycle_faithfullyFlat_tensor _ _ c₀ hcoc (Ideal.comap (Y.presheaf.germ V₀ y hyV₀).hom (IsLocalRing.maximalIdeal _)) inferInstance`. Establish `hm' : ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom m * (res hle c).val = ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom m`. Use `congrArg e hm` as an intermediate fact. Rewrite `this` using `[map_mul, he, he]`.

Simplify `this` using `[c₀]`. Take `⟨u, hu⟩` from `GlobalTheory.T.exists_unit_basicOpen_of_coboundary_identity f V V₀ h hle c r m s n hm' hs`. Use `⟨Y.basicOpen r, (Y.basicOpen_le r).trans hV₀V, ?_, u, hu⟩` and prove the remaining obligations. Rewrite using `[Scheme.mem_basicOpen _ _ _ hyV₀]`. Assume the negation of the conclusion as `hh`.

Conclude with `hr (by simpa [IsLocalRing.mem_maximalIdeal] using hh)`.
-/
theorem coboundary_locally_of_cocycle : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]
    (V : Y.Opens) (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
    (∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c) →
    ∀ y ∈ V, ∃ V' : Y.Opens, V' ≤ V ∧ y ∈ V' ∧ ∃ u : Γ(X, f ⁻¹ᵁ V')ˣ,
      ∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ V' →
        gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u := by
  intro X Y f _ _ _ _ V c hc y hy
  obtain ⟨V₀, hV₀, hyV₀, hV₀V⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hy
  have h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀ := fun z hz => by
    show f (pullback.snd f f z) ∈ V₀
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact hz
  have hle : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V := fun z hz => hV₀V hz
  letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
  obtain ⟨hN, hF, hFF⟩ := GlobalTheory.T.finite_faithfullyFlat_algebra_over_affine_open f V₀ hV₀
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_tensorSquare_equiv_fibreSquare_sections f V₀ hV₀ h
  have hcoc := GlobalTheory.T.unit_cocycle_descends_on_triple_overlaps f V V₀ hV₀ h hle c hc e he
  let c₀ : (Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀))ˣ := Units.map e.symm.toMonoidHom (res hle c)
  obtain ⟨r, hr, m, s, n, hm, hs⟩ := GlobalTheory.T.hilbert90_of_cocycle_faithfullyFlat_tensor _ _ c₀ hcoc
    (Ideal.comap (Y.presheaf.germ V₀ y hyV₀).hom (IsLocalRing.maximalIdeal _)) inferInstance
  have hm' : ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom m * (res hle c).val =
      ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom m := by
    have := congrArg e hm
    rw [map_mul, he, he] at this
    simpa [c₀] using this
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_unit_basicOpen_of_coboundary_identity f V V₀ h hle c r m s n hm' hs
  refine ⟨Y.basicOpen r, (Y.basicOpen_le r).trans hV₀V, ?_, u, hu⟩
  rw [Scheme.mem_basicOpen _ _ _ hyV₀]
  by_contra hh
  exact hr (by simpa [IsLocalRing.mem_maximalIdeal] using hh)

end GlobalTheory.LBDescent
