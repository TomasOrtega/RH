import Development.EtaleCohomology.EtaleSheaves.NbIsoPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.FlatMonoLimPf

/- English proof (translation)
Establish `hs : Surjective (pullback.fst t m)`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← Set.range_eq_univ, Scheme.Pullback.range_fst]`. Conclude with `Set.eq_univ_of_forall fun x => h ⟨x, rfl⟩`. Establish `: IsIso (pullback.fst t m)` using `Flat.isIso_of_surjective_of_mono _`.

Use `⟨inv (pullback.fst t m) ≫ pullback.snd t m, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]`.
-/
theorem exists_lift {X Y T : Scheme.{0}} (m : X ⟶ Y) [Mono m] [Flat m] [QuasiCompact m] (t : T ⟶ Y)
    (h : Set.range t ⊆ Set.range m) : ∃ b : T ⟶ X, b ≫ m = t := by
  have hs : Surjective (pullback.fst t m) := by
    constructor
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst]
    exact Set.eq_univ_of_forall fun x => h ⟨x, rfl⟩
  have : IsIso (pullback.fst t m) := Flat.isIso_of_surjective_of_mono _
  refine ⟨inv (pullback.fst t m) ≫ pullback.snd t m, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

/- English proof (translation)
Introduce `Y J _ _ D ι hι hc X m hm hf hq hr c hl`. Establish `ho : ∀ j, IsOpenImmersion (ι j)` using `fun j => (hι j).1`. Establish `hsub : ∀ j, Set.range m ⊆ Set.range (ι j)` using `fun j => hr ▸ Set.iInter_subset _ j`. Establish `hind : ∀ j k, c.π.app j ≫ ι j = c.π.app k ≫ ι k`. Introduce `j k`.

Rewrite using `[← c.w (IsCofiltered.minToLeft j k), ← c.w (IsCofiltered.minToRight j k), Category.assoc, Category.assoc, hc, hc]`. Take `⟨j0⟩ : Nonempty J` from `IsCofiltered.nonempty`. Establish `hp : Set.range (c.π.app j0 ≫ ι j0) ⊆ Set.range m`. Rewrite using `[hr]`. Use `Set.subset_iInter fun j => ?_` and prove the remaining obligations.

Rewrite using `[hind j0 j]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨c.π.app j x, (Scheme.Hom.comp_apply _ _ _).symm⟩`. Take `⟨b, hb⟩` from `exists_lift m _ hp`. Set `s : Cone D` to `{ pt := X π := { app := fun j => IsOpenImmersion.lift (ι j) m (hsub j) naturality := fun j k f => by`.

Rewrite using `[← cancel_mono (ι k)]`. Simplify using `[hc] } }`. Establish `hs : ∀ j, hl.lift s ≫ c.π.app j ≫ ι j = m`. Introduce `j`. Rewrite using `[hl.fac_assoc]`.

Conclude with `IsOpenImmersion.lift_fac _ _ _`. Use `⟨⟨b, hl.lift s, ?_, ?_⟩⟩` and prove the remaining obligations. Use `hl.hom_ext fun j => ?_` and prove the remaining obligations. Rewrite using `[← cancel_mono (ι j)]`. Simplify using `only [Category.assoc]`.

Use `erw [hs j, hb, Category.id_comp]`. Conclude with `hind j0 j`. Rewrite using `[← cancel_mono m, Category.assoc, hb, hs, Category.id_comp]`.
-/
theorem FlatMonoLim_of : LateralTheory.E.NbIsoPf.FlatMonoLim := by
  intro Y J _ _ D ι hι hc X m hm hf hq hr c hl
  have ho : ∀ j, IsOpenImmersion (ι j) := fun j => (hι j).1
  have hsub : ∀ j, Set.range m ⊆ Set.range (ι j) := fun j => hr ▸ Set.iInter_subset _ j
  have hind : ∀ j k, c.π.app j ≫ ι j = c.π.app k ≫ ι k := by
    intro j k
    rw [← c.w (IsCofiltered.minToLeft j k), ← c.w (IsCofiltered.minToRight j k), Category.assoc, Category.assoc,
      hc, hc]
  obtain ⟨j0⟩ : Nonempty J := IsCofiltered.nonempty
  have hp : Set.range (c.π.app j0 ≫ ι j0) ⊆ Set.range m := by
    rw [hr]
    refine Set.subset_iInter fun j => ?_
    rw [hind j0 j]
    rintro _ ⟨x, rfl⟩
    exact ⟨c.π.app j x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  obtain ⟨b, hb⟩ := exists_lift m _ hp
  let s : Cone D :=
    { pt := X
      π :=
        { app := fun j => IsOpenImmersion.lift (ι j) m (hsub j)
          naturality := fun j k f => by
            rw [← cancel_mono (ι k)]
            simp [hc] } }
  have hs : ∀ j, hl.lift s ≫ c.π.app j ≫ ι j = m := by
    intro j
    rw [hl.fac_assoc]
    exact IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨b, hl.lift s, ?_, ?_⟩⟩
  · refine hl.hom_ext fun j => ?_
    rw [← cancel_mono (ι j)]
    simp only [Category.assoc]
    erw [hs j, hb, Category.id_comp]
    exact hind j0 j
  · rw [← cancel_mono m, Category.assoc, hb, hs, Category.id_comp]

end LateralTheory.E.FlatMonoLimPf
