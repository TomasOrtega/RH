import Mathlib

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.QuotientSide

/- English proof (translation)
Substitute `w` using the available equality. Set `m : pullback (r ≫ g) (r ≫ g) ⟶ pullback g g` to `pullback.map _ _ _ _ r r (𝟙 S) (by simp) (by simp)`. Establish `hm : IsFinite m` using `MorphismProperty.pullbackMap (P := @IsFinite) (i₁ := r) (i₂ := r) inferInstance inferInstance`. Use `rfl rfl`. Establish `comm : pullback.diagonal (r ≫ g) ≫ m = r ≫ pullback.diagonal g`.

Establish `h₁ : m ≫ pullback.fst g g = pullback.fst (r ≫ g) (r ≫ g) ≫ r` using `pullback.lift_fst _ _ _`. Establish `h₂ : m ≫ pullback.snd g g = pullback.snd (r ≫ g) (r ≫ g) ≫ r` using `pullback.lift_snd _ _ _`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, h₁, ← Category.assoc, pullback.diagonal_fst, pullback.diagonal_fst, Category.id_comp, Category.comp_id]`. Rewrite using `[Category.assoc, Category.assoc, h₂, ← Category.assoc, pullback.diagonal_snd, pullback.diagonal_snd, Category.id_comp, Category.comp_id]`.

Establish `hrange : Set.range (pullback.diagonal g) = m '' Set.range (pullback.diagonal (r ≫ g))`. Rewrite using `[← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, comm, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr r.surjective, Set.image_univ]`. Establish `hclosed : IsClosed (Set.range (pullback.diagonal g))`. Rewrite using `[hrange]`. Conclude with `m.isClosedMap _ (pullback.diagonal (r ≫ g)).isClosedEmbedding.isClosed_range`.

Conclude with `⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩`.
-/
theorem isSeparated_of_finite_surjective {S X Y : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S)
    (r : X ⟶ Y) (w : r ≫ g = f) [IsSeparated f] [IsFinite r] [Surjective r] : IsSeparated g := by
  subst w
  let m : pullback (r ≫ g) (r ≫ g) ⟶ pullback g g :=
    pullback.map _ _ _ _ r r (𝟙 S) (by simp) (by simp)
  have hm : IsFinite m :=
    MorphismProperty.pullbackMap (P := @IsFinite) (i₁ := r) (i₂ := r) inferInstance inferInstance
      rfl rfl
  have comm : pullback.diagonal (r ≫ g) ≫ m = r ≫ pullback.diagonal g := by
    have h₁ : m ≫ pullback.fst g g = pullback.fst (r ≫ g) (r ≫ g) ≫ r := pullback.lift_fst _ _ _
    have h₂ : m ≫ pullback.snd g g = pullback.snd (r ≫ g) (r ≫ g) ≫ r := pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, h₁, ← Category.assoc, pullback.diagonal_fst,
        pullback.diagonal_fst, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, Category.assoc, h₂, ← Category.assoc, pullback.diagonal_snd,
        pullback.diagonal_snd, Category.id_comp, Category.comp_id]
  have hrange : Set.range (pullback.diagonal g) =
      m '' Set.range (pullback.diagonal (r ≫ g)) := by
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, comm,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr r.surjective, Set.image_univ]
  have hclosed : IsClosed (Set.range (pullback.diagonal g)) := by
    rw [hrange]
    exact m.isClosedMap _ (pullback.diagonal (r ≫ g)).isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩

/- English proof (translation)
Introduce `S X Y K q p₁ p₂ _ _ hX hq hs`. Conclude with `isSeparated_of_finite_surjective X.hom Y.hom q.left (Over.w q)`.
-/
theorem isSeparated_target_of_finite_surjective :
    ∀ {S : Scheme.{0}} {X Y K : Over S} (q : X ⟶ Y) (p₁ p₂ : K ⟶ X), IsPullback p₁ p₂ q q →
      IsFinite p₂.left → IsSeparated X.hom → IsFinite q.left → Surjective q.left →
      IsSeparated Y.hom := by
  intro S X Y K q p₁ p₂ _ _ hX hq hs
  exact isSeparated_of_finite_surjective X.hom Y.hom q.left (Over.w q)

end GlobalTheory.CompanionTheory.QuotientSide
