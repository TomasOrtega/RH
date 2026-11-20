import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Introduce `G _ A B f g n j h hB z`. Establish `hc : groupHomology.chainsMap (MonoidHom.id G) (f ≫ g) = n • 𝟙 (groupHomology.inhomogeneousChains A)`. Use extensionality with `i : 1`. Apply `ModuleCat.hom_ext` to reduce the goal to its premises. Use `DFunLike.ext _ _ fun c => ?_` and prove the remaining obligations.

Use `Finsupp.ext fun y => ?_` and prove the remaining obligations. Simplify using `[h]`. Establish `hm : groupHomology.map (MonoidHom.id G) (f ≫ g) j = n • 𝟙 (groupHomology A j)`. Simplify using `only [groupHomology.map, hc]`. Express the relevant statement in the definitionally equal form `(HomologicalComplex.homologyFunctor _ _ j).map _ = _`.

Rewrite using `[Functor.map_nsmul, CategoryTheory.Functor.map_id]`. Both sides reduce to the same expression. Establish `e1 : (groupHomology.map (MonoidHom.id G) (f ≫ g) j).hom z = n • z`. Rewrite using `[hm]`. Both sides reduce to the same expression.

Rewrite using `[← e1, groupHomology.map_id_comp]`. Establish `e2 : (groupHomology.map (MonoidHom.id G) f j).hom z = 0` using `Subsingleton.elim (α := groupHomology B j) _ _`. Simplify using `[e2]`.
-/
theorem UpperTheory.V.KH.mapNsmul :
    ∀ (G : Type) [Group G] (A B : Rep ℤ G) (f : A ⟶ B) (g : B ⟶ A) (n j : ℕ),
      (∀ a, g.hom (f.hom a) = n • a) → Subsingleton (groupHomology B j) →
      ∀ z : groupHomology A j, n • z = 0 := by
  intro G _ A B f g n j h hB z
  have hc : groupHomology.chainsMap (MonoidHom.id G) (f ≫ g) =
      n • 𝟙 (groupHomology.inhomogeneousChains A) := by
    ext i : 1
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun c => ?_
    refine Finsupp.ext fun y => ?_
    simp [h]
  have hm : groupHomology.map (MonoidHom.id G) (f ≫ g) j = n • 𝟙 (groupHomology A j) := by
    simp only [groupHomology.map, hc]
    change (HomologicalComplex.homologyFunctor _ _ j).map _ = _
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  have e1 : (groupHomology.map (MonoidHom.id G) (f ≫ g) j).hom z = n • z := by
    rw [hm]
    rfl
  rw [← e1, groupHomology.map_id_comp]
  have e2 : (groupHomology.map (MonoidHom.id G) f j).hom z = 0 :=
    Subsingleton.elim (α := groupHomology B j) _ _
  simp [e2]
