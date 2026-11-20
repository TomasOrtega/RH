import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GeomSurj

/- English proof (translation)
Establish `hs : Surjective (spMap σ)` using `⟨fun y ↦ by`. Take `⟨z⟩ : Nonempty ↥(Sp K)` from `inferInstance`. Conclude with `⟨z, Subsingleton.elim _ _⟩⟩`. Establish `hJ : JacobsonSpace ↥(pullback a (spMap σ))` using `LocallyOfFiniteType.jacobsonSpace (pullback.snd a (spMap σ))`. Establish `hZ : IsClosed ((pullback.fst a (spMap σ)) ⁻¹' Set.range ψ)` using `hψ.preimage (pullback.fst a (spMap σ)).continuous`.

Establish `hsub : closedPoints ↥(pullback a (spMap σ)) ⊆ (pullback.fst a (spMap σ)) ⁻¹' Set.range ψ`. Introduce `z hz`. Use `replace hz : IsClosed {z} := hz`. Take `⟨p, hp⟩` from `h (pointOfClosedPoint (pullback.snd a (spMap σ)) z hz ≫ pullback.fst _ _) (by rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc])`. Take `⟨w⟩ : Nonempty ↥(Sp K)` from `inferInstance`.

Use `⟨p w, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← hp, Scheme.Hom.comp_apply, pointOfClosedPoint_apply]`. Establish `hall` using `closure_minimal hsub hZ`. Rewrite `hall` using `[closure_closedPoints]`. Use `⟨fun y ↦ ?_⟩` and prove the remaining obligations.

Take `⟨z, rfl⟩` from `(pullback.fst a (spMap σ)).surjective y`. Conclude with `hall (Set.mem_univ z)`.
-/
theorem surjective_of_points {k K : Type} [Field k] [Field K] [IsAlgClosed K] (σ : k →+* K)
    {P A : Scheme.{0}} (a : A ⟶ Sp k) [LocallyOfFiniteType a] (ψ : P ⟶ A)
    (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Sp K ⟶ A, x ≫ a = spMap σ → ∃ p : Sp K ⟶ P, x = p ≫ ψ) : Surjective ψ := by
  have hs : Surjective (spMap σ) := ⟨fun y ↦ by
    obtain ⟨z⟩ : Nonempty ↥(Sp K) := inferInstance
    exact ⟨z, Subsingleton.elim _ _⟩⟩
  have hJ : JacobsonSpace ↥(pullback a (spMap σ)) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd a (spMap σ))
  have hZ : IsClosed ((pullback.fst a (spMap σ)) ⁻¹' Set.range ψ) :=
    hψ.preimage (pullback.fst a (spMap σ)).continuous
  have hsub : closedPoints ↥(pullback a (spMap σ)) ⊆
      (pullback.fst a (spMap σ)) ⁻¹' Set.range ψ := by
    intro z hz
    replace hz : IsClosed {z} := hz
    obtain ⟨p, hp⟩ := h (pointOfClosedPoint (pullback.snd a (spMap σ)) z hz ≫ pullback.fst _ _)
      (by rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc])
    obtain ⟨w⟩ : Nonempty ↥(Sp K) := inferInstance
    refine ⟨p w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hp, Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  have hall := closure_minimal hsub hZ
  rw [closure_closedPoints] at hall
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨z, rfl⟩ := (pullback.fst a (spMap σ)).surjective y
  exact hall (Set.mem_univ z)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
open scoped CategoryTheory.Obj in

/- English proof (translation)
Establish `hΩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω = Spec (CommRingCat.of Ω)` using `rfl`. Use `haveI : JacobsonSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω) := by rw [hΩ]; infer_instance`. Use `haveI : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω) := by rw [hΩ]; infer_instance`. Use `haveI : JacobsonSpace (pullback ψ x :) := LocallyOfFiniteType.jacobsonSpace (pullback.snd ψ x)`. Take `⟨q₀, -⟩` from `(pullback.snd ψ x).surjective (Classical.arbitrary _)`.

Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : (closedPoints (pullback ψ x :)).Nonempty := by`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[Set.not_nonempty_iff_eq_empty]`. Establish `hc` using `closure_closedPoints (X := (pullback ψ x :))`. Rewrite `hc` using `[h, closure_empty]`.

Conclude with `(hc ▸ Set.mem_univ q₀ : q₀ ∈ (∅ : Set _))`. Use `haveI : LocallyOfFiniteType ((pullback ψ x).fromSpecResidueField q) := isClosed_singleton_iff_locallyOfFiniteType.mp hq`. Set `g : Spec ((pullback ψ x).residueField q) ⟶ Spec (CommRingCat.of Ω)` to `(pullback ψ x).fromSpecResidueField q ≫ pullback.snd ψ x`. Establish `hg : LocallyOfFiniteType (Spec.map (Spec.preimage g))`. Rewrite using `[Spec.map_preimage]`.

Simplify using `only [g]`. Use `infer_instance`. Establish `hft` using `HasRingHomProperty.Spec_iff.mp hg`. Use `set f := Spec.preimage g with hf`. Use `letI : Algebra Ω ((pullback ψ x).residueField q) := f.hom.toAlgebra`.

Use `haveI : Algebra.FiniteType Ω ((pullback ψ x).residueField q) := hft`. Use `haveI : Module.Finite Ω ((pullback ψ x).residueField q) := finite_of_finite_type_of_isJacobsonRing _ _`. Set `φ : (pullback ψ x).residueField q →ₐ[Ω] Ω` to `IsAlgClosed.lift`. Establish `key : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g = 𝟙 _`. Rewrite using `[← Spec.map_preimage g, ← hf, ← Spec.map_comp]`.

Use `Spec.map_id (CommRingCat.of Ω)` and compare the differences between its conclusion and the goal. Use extensionality with `a`. Conclude with `φ.commutes a`. Use `⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pullback ψ x).fromSpecResidueField q ≫ pullback.fst ψ x, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (Scheme.fromSpecResidueField _ _), ← Category.assoc]`.

Express the relevant statement in the definitionally equal form `x = (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g) ≫ x`. Rewrite using `[key, Category.id_comp]`.
-/
theorem _root_.GlobalTheory.GeomSurj.exists_lift_of_surjective {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P A : Scheme.{0}}
    (ψ : P ⟶ A) [LocallyOfFiniteType ψ] [Surjective ψ] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ A) :
    ∃ p : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ P, x = p ≫ ψ := by
  have hΩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω = Spec (CommRingCat.of Ω) := rfl
  haveI : JacobsonSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω) := by rw [hΩ]; infer_instance
  haveI : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω) := by rw [hΩ]; infer_instance
  haveI : JacobsonSpace (pullback ψ x :) := LocallyOfFiniteType.jacobsonSpace (pullback.snd ψ x)
  obtain ⟨q₀, -⟩ := (pullback.snd ψ x).surjective (Classical.arbitrary _)
  obtain ⟨q, hq⟩ : (closedPoints (pullback ψ x :)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hc := closure_closedPoints (X := (pullback ψ x :))
    rw [h, closure_empty] at hc
    exact (hc ▸ Set.mem_univ q₀ : q₀ ∈ (∅ : Set _))
  haveI : LocallyOfFiniteType ((pullback ψ x).fromSpecResidueField q) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hq
  let g : Spec ((pullback ψ x).residueField q) ⟶ Spec (CommRingCat.of Ω) :=
    (pullback ψ x).fromSpecResidueField q ≫ pullback.snd ψ x
  have hg : LocallyOfFiniteType (Spec.map (Spec.preimage g)) := by
    rw [Spec.map_preimage]; dsimp only [g]; infer_instance
  have hft := HasRingHomProperty.Spec_iff.mp hg
  set f := Spec.preimage g with hf
  letI : Algebra Ω ((pullback ψ x).residueField q) := f.hom.toAlgebra
  haveI : Algebra.FiniteType Ω ((pullback ψ x).residueField q) := hft
  haveI : Module.Finite Ω ((pullback ψ x).residueField q) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  let φ : (pullback ψ x).residueField q →ₐ[Ω] Ω := IsAlgClosed.lift
  have key : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g = 𝟙 _ := by
    rw [← Spec.map_preimage g, ← hf, ← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of Ω)
    ext a
    exact φ.commutes a
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pullback ψ x).fromSpecResidueField q ≫
    pullback.fst ψ x, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition,
    ← Category.assoc (Scheme.fromSpecResidueField _ _), ← Category.assoc]
  change x = (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g) ≫ x
  rw [key, Category.id_comp]

end GlobalTheory.GeomSurj
