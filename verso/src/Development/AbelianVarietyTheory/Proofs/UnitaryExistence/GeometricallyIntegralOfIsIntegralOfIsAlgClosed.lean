import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory

universe u

/- English proof (translation)
Use `⟨fun K _ y Z p q h => ?_⟩` and prove the remaining obligations. Use `LocallyOfFiniteType.jacobsonSpace f` as an intermediate fact. Establish `hy : Surjective y` using `⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩`. Establish `hs : Surjective p` using `MorphismProperty.of_isPullback h.flip hy`. Establish `ho : UniversallyOpen p` using `MorphismProperty.of_isPullback h.flip (inferInstance : UniversallyOpen y)`.

Establish `fib : ∀ x : X, IsClosed {x} → ∀ a b : Z, p a = x → p b = x → a = b`. Introduce `x hx a b ha hb`. Set `s` to `pointOfClosedPoint f x hx`. Establish `hs : s ≫ f = 𝟙 _` using `pointOfClosedPoint_comp f x hx`. Set `t : Spec (.of K) ⟶ Z` to `h.lift (y ≫ s) (𝟙 _) (by simp [hs])`.

Establish `ht : IsPullback t y p s`. Use `IsPullback.of_right (h₁₂ := q) (v₁₃ := y) (h₂₂ := f) ?_ (by simp [t]) h.flip` and prove the remaining obligations. Rewrite using `[hs, show t ≫ q = 𝟙 _ by simp [t]]`. Conclude with `IsPullback.of_id_fst`. Take `⟨a', rfl, -⟩` from `Scheme.exists_preimage_of_isPullback ht a (IsLocalRing.closedPoint k) (ha.trans (pointOfClosedPoint_apply f x hx _).symm)`.

Take `⟨b', rfl, -⟩` from `Scheme.exists_preimage_of_isPullback ht b (IsLocalRing.closedPoint k) (hb.trans (pointOfClosedPoint_apply f x hx _).symm)`. Rewrite using `[Subsingleton.elim a' b']`. Establish `hne : Nonempty Z` using `(p.surjective (Classical.arbitrary X)).nonempty`. Establish `: PreirreducibleSpace Z` using `⟨fun U V hU hV hU' hV' => by`. Rewrite `hU'`, `hV'`, the goal using `[Set.univ_inter]`.

Establish `o₁ : IsOpen (p '' U)` using `p.isOpenMap _ hU`. Establish `o₂ : IsOpen (p '' V)` using `p.isOpenMap _ hV`. Take `⟨x, ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩, hxc⟩` from `nonempty_inter_closedPoints (nonempty_preirreducible_inter o₁ o₂ (hU'.image _) (hV'.image _)) (o₁.inter o₂).isLocallyClosed`. Conclude with `⟨a, ha, fib x hxc a b hax hbx ▸ hb⟩⟩`. Conclude with `⟨hne⟩`.
-/
theorem geometricallyIrreducible_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IrreducibleSpace X] :
    GeometricallyIrreducible f := by
  refine ⟨fun K _ y Z p q h => ?_⟩
  have := LocallyOfFiniteType.jacobsonSpace f
  have hy : Surjective y := ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hs : Surjective p := MorphismProperty.of_isPullback h.flip hy
  have ho : UniversallyOpen p := MorphismProperty.of_isPullback h.flip
    (inferInstance : UniversallyOpen y)

  have fib : ∀ x : X, IsClosed {x} → ∀ a b : Z, p a = x → p b = x → a = b := by
    intro x hx a b ha hb
    let s := pointOfClosedPoint f x hx
    have hs : s ≫ f = 𝟙 _ := pointOfClosedPoint_comp f x hx
    let t : Spec (.of K) ⟶ Z := h.lift (y ≫ s) (𝟙 _) (by simp [hs])
    have ht : IsPullback t y p s := by
      refine IsPullback.of_right (h₁₂ := q) (v₁₃ := y) (h₂₂ := f) ?_ (by simp [t]) h.flip
      rw [hs, show t ≫ q = 𝟙 _ by simp [t]]
      exact IsPullback.of_id_fst
    obtain ⟨a', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht a (IsLocalRing.closedPoint k)
      (ha.trans (pointOfClosedPoint_apply f x hx _).symm)
    obtain ⟨b', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht b (IsLocalRing.closedPoint k)
      (hb.trans (pointOfClosedPoint_apply f x hx _).symm)
    rw [Subsingleton.elim a' b']
  have hne : Nonempty Z := (p.surjective (Classical.arbitrary X)).nonempty
  have : PreirreducibleSpace Z := ⟨fun U V hU hV hU' hV' => by
    rw [Set.univ_inter] at hU' hV' ⊢
    have o₁ : IsOpen (p '' U) := p.isOpenMap _ hU
    have o₂ : IsOpen (p '' V) := p.isOpenMap _ hV
    obtain ⟨x, ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩, hxc⟩ := nonempty_inter_closedPoints
      (nonempty_preirreducible_inter o₁ o₂ (hU'.image _) (hV'.image _))
      (o₁.inter o₂).isLocallyClosed
    exact ⟨a, ha, fib x hxc a b hax hbx ▸ hb⟩⟩
  exact ⟨hne⟩

/- English proof (translation)
Introduce `k _ _ X _ h`. Establish `h₁ : GeometricallyReduced X.hom` using `ReducedSubgroup.geometricallyReduced_of_perfectField (k := k) X.hom`. Establish `h₂ : GeometricallyIrreducible X.hom` using `geometricallyIrreducible_of_isAlgClosed (k := k) X.hom`. Conclude with `GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible X.hom`.
-/
theorem geometricallyIntegral_of_isIntegral_of_isAlgClosed :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Over (Sp k)) [IsIntegral X.left],
      LocallyOfFiniteType X.hom → GeometricallyIntegral X.hom := by
  intro k _ _ X _ h
  have h₁ : GeometricallyReduced X.hom :=
    ReducedSubgroup.geometricallyReduced_of_perfectField (k := k) X.hom
  have h₂ : GeometricallyIrreducible X.hom :=
    geometricallyIrreducible_of_isAlgClosed (k := k) X.hom
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible X.hom

end GlobalTheory
