import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Establish `hJ : JacobsonSpace P` using `LocallyOfFiniteType.jacobsonSpace s`. Establish `hc : (closedPoints P).Finite`. Establish `: Finite (closedPoints P)` using `Finite.of_equiv _ (pointEquivClosedPoint s)`. Conclude with `Set.toFinite _`. Establish `hcl : IsClosed (closedPoints P)`.

Rewrite using `[← Set.biUnion_of_singleton (closedPoints P)]`. Conclude with `hc.isClosed_biUnion fun x hx ↦ hx`. Establish `hu : closedPoints P = Set.univ`. Use `JacobsonSpace.closure_inter_closedPoints (X := P) isClosed_univ` as an intermediate fact. Rewrite `this` using `[Set.univ_inter, hcl.closure_eq]`. Then use the resulting hypothesis.

Conclude with `Set.finite_univ_iff.mp (hu ▸ hc)`.
-/
theorem finite_of_finite_sections {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P : Scheme.{0}}
    (s : P ⟶ Spec (.of Ω)) [LocallyOfFiniteType s]
    (h : Finite {x : Spec (.of Ω) ⟶ P // x ≫ s = 𝟙 _}) : Finite P := by
  have hJ : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace s
  have hc : (closedPoints P).Finite := by
    have : Finite (closedPoints P) := Finite.of_equiv _ (pointEquivClosedPoint s)
    exact Set.toFinite _
  have hcl : IsClosed (closedPoints P) := by
    rw [← Set.biUnion_of_singleton (closedPoints P)]
    exact hc.isClosed_biUnion fun x hx ↦ hx
  have hu : closedPoints P = Set.univ := by
    have := JacobsonSpace.closure_inter_closedPoints (X := P) isClosed_univ
    rwa [Set.univ_inter, hcl.closure_eq] at this
  exact Set.finite_univ_iff.mp (hu ▸ hc)

/- English proof (translation)
Use `LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_` and prove the remaining obligations. Set `Ω` to `AlgebraicClosure (Y.residueField y)`. Set `y' : Spec (.of Ω) ⟶ Y` to `Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫ Y.fromSpecResidueField y`. Establish `hy : y ∈ Set.range y'`. Take `⟨z⟩ : Nonempty ↥(Spec (.of Ω))` from `inferInstance`.

Conclude with `⟨z, (Scheme.Hom.comp_apply _ _ z).trans (Scheme.fromSpecResidueField_apply y _)⟩`. Use `clear_value y'`. Use `h Ω y'` as an intermediate fact. Establish `hP : Finite ↥(pullback f y')`. Use `finite_of_finite_sections (pullback.snd f y') ?_` and prove the remaining obligations.

Use `Finite.of_injective (β := {x : Spec (.of Ω) ⟶ X // x ≫ f = y'}) (fun x ↦ ⟨x.1 ≫ pullback.fst f y', by` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp]⟩) ?_`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises.

Conclude with `congrArg Subtype.val hab`. Rewrite using `[a.2, b.2]`. Use `(Set.finite_range (pullback.fst f y')).subset ?_` and prove the remaining obligations. Rewrite using `[Scheme.Pullback.range_fst]`. Conclude with `Set.preimage_mono (Set.singleton_subset_iff.mpr hy)`.
-/
theorem locallyQuasiFinite_of_finite_geometric_points {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyOfFiniteType f]
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) : LocallyQuasiFinite f := by
  refine LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_
  let Ω := AlgebraicClosure (Y.residueField y)
  let y' : Spec (.of Ω) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫ Y.fromSpecResidueField y
  have hy : y ∈ Set.range y' := by
    obtain ⟨z⟩ : Nonempty ↥(Spec (.of Ω)) := inferInstance
    exact ⟨z, (Scheme.Hom.comp_apply _ _ z).trans (Scheme.fromSpecResidueField_apply y _)⟩
  clear_value y'
  have := h Ω y'
  have hP : Finite ↥(pullback f y') := by
    refine finite_of_finite_sections (pullback.snd f y') ?_
    refine Finite.of_injective (β := {x : Spec (.of Ω) ⟶ X // x ≫ f = y'})
      (fun x ↦ ⟨x.1 ≫ pullback.fst f y', by
        rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp]⟩) ?_
    intro a b hab
    apply Subtype.ext
    apply pullback.hom_ext
    · exact congrArg Subtype.val hab
    · rw [a.2, b.2]
  refine (Set.finite_range (pullback.fst f y')).subset ?_
  rw [Scheme.Pullback.range_fst]
  exact Set.preimage_mono (Set.singleton_subset_iff.mpr hy)

/- English proof (translation)
Break down `isEmpty_or_nonempty {x : T ⟶ Ga // x ≫ p = y} with he | ⟨⟨x₀, hx₀⟩⟩` into its components or cases. Use `infer_instance`. Use `Finite.of_injective (β := {x : T ⟶ Ga // x ≫ p = 1}) (fun x ↦ ⟨x₀⁻¹ * x.1, by` and prove the remaining obligations. Rewrite using `[MonObj.mul_comp, GrpObj.inv_comp, hx₀, x.2, inv_mul_cancel]⟩) ?_`. Introduce `a b hab`.

Conclude with `Subtype.ext (mul_left_cancel (congrArg Subtype.val hab))`.
-/
theorem finite_fiber_of_finite_ker {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {Ga G T : C} [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G) [IsMonHom p]
    (h : Finite {x : T ⟶ Ga // x ≫ p = 1}) (y : T ⟶ G) :
    Finite {x : T ⟶ Ga // x ≫ p = y} := by
  rcases isEmpty_or_nonempty {x : T ⟶ Ga // x ≫ p = y} with he | ⟨⟨x₀, hx₀⟩⟩
  · infer_instance
  refine Finite.of_injective (β := {x : T ⟶ Ga // x ≫ p = 1})
    (fun x ↦ ⟨x₀⁻¹ * x.1, by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hx₀, x.2, inv_mul_cancel]⟩) ?_
  intro a b hab
  exact Subtype.ext (mul_left_cancel (congrArg Subtype.val hab))

/- English proof (translation)
Introduce `S Ga G _ _ p hp hft _ h`. Use `locallyQuasiFinite_of_finite_geometric_points p.left fun Ω _ _ y ↦ ?_` and prove the remaining obligations. Set `y' : Over.mk (y ≫ G.hom) ⟶ G` to `Over.homMk y rfl`. Use `finite_fiber_of_finite_ker p (h Ω (y ≫ G.hom)) y'` as an intermediate fact. Use `Finite.of_injective (β := {x : Over.mk (y ≫ G.hom) ⟶ Ga // x ≫ p = y'}) (fun x ↦ ⟨Over.homMk x.1 (by` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `x.1 ≫ Ga.hom = y ≫ G.hom`. Rewrite using `[← Over.w p, ← Category.assoc, x.2]), Over.OverMorphism.ext x.2⟩) ?_`. Introduce `a b hab`. Conclude with `Subtype.ext (congrArg (fun z ↦ z.1.left) hab)`.
-/
theorem locallyQuasiFinite_of_finite_geometric_ker :
    ∀ (S : Scheme.{0}) (Ga G : Over S) [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G), IsMonHom p →
      LocallyOfFiniteType p.left → QuasiCompact p.left →
      (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S),
        Finite {x : Over.mk t ⟶ Ga // x ≫ p = 1}) → LocallyQuasiFinite p.left := by
  intro S Ga G _ _ p hp hft _ h
  refine locallyQuasiFinite_of_finite_geometric_points p.left fun Ω _ _ y ↦ ?_
  let y' : Over.mk (y ≫ G.hom) ⟶ G := Over.homMk y rfl
  have := finite_fiber_of_finite_ker p (h Ω (y ≫ G.hom)) y'
  refine Finite.of_injective (β := {x : Over.mk (y ≫ G.hom) ⟶ Ga // x ≫ p = y'})
    (fun x ↦ ⟨Over.homMk x.1 (by
      change x.1 ≫ Ga.hom = y ≫ G.hom
      rw [← Over.w p, ← Category.assoc, x.2]), Over.OverMorphism.ext x.2⟩) ?_
  intro a b hab
  exact Subtype.ext (congrArg (fun z ↦ z.1.left) hab)

end GlobalTheory
