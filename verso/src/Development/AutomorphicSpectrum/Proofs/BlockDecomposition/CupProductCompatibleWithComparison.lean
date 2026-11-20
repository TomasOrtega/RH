import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.DictCup

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

/- English proof (translation)
Substitute `hc` using the available equality. Take `rfl` from `eq_of_heq hg`. Both sides reduce to the same expression.
-/
theorem mp_val_congr (x : Cn F 1) {c c' : Fin (1 + 1) ⥤ C} (hc : c = c') {T : C}
    (g : c.obj (Fin.last 1) ⟶ T) (g' : c'.obj (Fin.last 1) ⟶ T) (hg : HEq g g') :
    mp F g (x c) = mp F g' (x c') := by
  subst hc
  obtain rfl := eq_of_heq hg
  rfl

/- English proof (translation)
Rewrite using `[show h = homOfLE (by decide) from Subsingleton.elim _ _]`. Both sides reduce to the same expression.
-/
theorem blockDecomposition_mk₂_fact {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : (0 : Fin 3) ⟶ 1) :
    (ComposableArrows.mk₂ φ ψ).map h = φ := by
  rw [show h = homOfLE (by decide) from Subsingleton.elim _ _]
  rfl

/- English proof (translation)
Rewrite using `[show h = homOfLE (by decide) from Subsingleton.elim _ _]`. Both sides reduce to the same expression.
-/
theorem composableArrows_mk₂_map_one_two {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : (1 : Fin 3) ⟶ 2) :
    (ComposableArrows.mk₂ φ ψ).map h = ψ := by
  rw [show h = homOfLE (by decide) from Subsingleton.elim _ _]
  rfl

/- English proof (translation)
Use `ComposableArrows.ext₁ rfl rfl ?_` and prove the remaining obligations. Use `show _ = 𝟙 _ ≫ φ ≫ 𝟙 _`. Rewrite using `[Category.id_comp, Category.comp_id]`. Conclude with `blockDecomposition_mk₂_fact φ ψ (homOfLE (by decide))`.
-/
theorem front_chain {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (fr 1).monotone.functor ⋙ ComposableArrows.mk₂ φ ψ = ComposableArrows.mk₁ φ := by
  refine ComposableArrows.ext₁ rfl rfl ?_
  show _ = 𝟙 _ ≫ φ ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact blockDecomposition_mk₂_fact φ ψ (homOfLE (by decide))

/- English proof (translation)
Use `ComposableArrows.ext₁ rfl rfl ?_` and prove the remaining obligations. Use `show _ = 𝟙 _ ≫ ψ ≫ 𝟙 _`. Rewrite using `[Category.id_comp, Category.comp_id]`. Conclude with `composableArrows_mk₂_map_one_two φ ψ (homOfLE (by decide))`.
-/
theorem face_chain {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (dl (0 : Fin (1 + 1 + 1))).monotone.functor ⋙ ComposableArrows.mk₂ φ ψ = ComposableArrows.mk₁ ψ := by
  refine ComposableArrows.ext₁ rfl rfl ?_
  show _ = 𝟙 _ ≫ ψ ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact composableArrows_mk₂_map_one_two φ ψ (homOfLE (by decide))

/- English proof (translation)
Establish `e₁ : pr F (fr 1) x (ComposableArrows.mk₂ φ ψ) = mp F ψ y`. Rewrite using `[pr_apply, ← hy]`. Use `mp_val_congr x (front_chain φ ψ) _ ψ (heq_of_eq (composableArrows_mk₂_map_one_two φ ψ _))` and prove the remaining obligations. Establish `e₂ : pr F (dl 0) x' (ComposableArrows.mk₂ φ ψ) = y'`. Rewrite using `[pr_apply, ← hy']`.

Use `(mp_val_congr x' (face_chain φ ψ) _ (𝟙 T'') (heq_of_eq ?_)).trans (mp_id F _ _)` and prove the remaining obligations. Conclude with `(ComposableArrows.mk₂ φ ψ).map_id _`. Rewrite using `[cup1_apply]`. Conclude with `congrArg₂ (· * ·) e₁ e₂`.
-/
theorem cup1_mk₂_eq_mp_mul (x x' : Cn F 1) {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'')
    (y : F.obj T') (y' : F.obj T'') (hy : x (ComposableArrows.mk₁ φ) = y)
    (hy' : x' (ComposableArrows.mk₁ ψ) = y') :
    cup1 F 1 x x' (ComposableArrows.mk₂ φ ψ) = mp F ψ y * y' := by
  have e₁ : pr F (fr 1) x (ComposableArrows.mk₂ φ ψ) = mp F ψ y := by
    rw [pr_apply, ← hy]
    refine mp_val_congr x (front_chain φ ψ) _ ψ (heq_of_eq (composableArrows_mk₂_map_one_two φ ψ _))
  have e₂ : pr F (dl 0) x' (ComposableArrows.mk₂ φ ψ) = y' := by
    rw [pr_apply, ← hy']
    refine (mp_val_congr x' (face_chain φ ψ) _ (𝟙 T'') (heq_of_eq ?_)).trans (mp_id F _ _)
    exact (ComposableArrows.mk₂ φ ψ).map_id _
  rw [cup1_apply]
  exact congrArg₂ (· * ·) e₁ e₂

end GlobalTheory.CompanionTheory.HopfC.DictCup

namespace GlobalTheory.CompanionTheory.HopfC

/- English proof (translation)
Introduce `R _ C _ F u₁ u₂ h₁ h₂ hx a b`. Take `⟨f, rfl⟩` from `H1.mk_surjective F a`. Take `⟨f', rfl⟩` from `H1.mk_surjective F b`. Take `⟨x, hf⟩` from `hx f`. Take `⟨x', hf'⟩` from `hx f'`.

Rewrite using `[h₁ f x hf, h₁ f' x' hf', Lc_mk, cup_mk]`. Use `h₂ (cupZ F f f') (cz F 1 x x') fun T T' T'' φ ψ ↦ ?_` and prove the remaining obligations. Rewrite using `[cz_val, cupZ_apply]`. Conclude with `DictCup.cup1_mk₂_eq_mp_mul x.1 x'.1 φ ψ _ _ (hf T T' φ) (hf' T' T'' ψ)`.
-/
theorem dict_cup : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (u₁ : H1 F →ₗ[R] HH F 1) (u₂ : H2 F →ₗ[R] HH F 2), IsIdealValuedLiftSystemCocycle F u₁ → IsDegreeTwoComparison F u₂ → (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) → ∀ a b, u₂ (cup F a b) = Lc F 1 (u₁ a) (u₁ b) := by
  intro R _ C _ F u₁ u₂ h₁ h₂ hx a b
  obtain ⟨f, rfl⟩ := H1.mk_surjective F a
  obtain ⟨f', rfl⟩ := H1.mk_surjective F b
  obtain ⟨x, hf⟩ := hx f
  obtain ⟨x', hf'⟩ := hx f'
  rw [h₁ f x hf, h₁ f' x' hf', Lc_mk, cup_mk]
  refine h₂ (cupZ F f f') (cz F 1 x x') fun T T' T'' φ ψ ↦ ?_
  rw [cz_val, cupZ_apply]
  exact DictCup.cup1_mk₂_eq_mp_mul x.1 x'.1 φ ψ _ _ (hf T T' φ) (hf' T' T'' ψ)

end GlobalTheory.CompanionTheory.HopfC
