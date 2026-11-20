import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteOfIsClosedTorusExtensionOfPowEqOne

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Use `haveI : Surjective (pullback.snd i a) := ⟨by`. Rewrite using `[← Set.range_eq_univ, Scheme.Pullback.range_snd]`. Conclude with `Set.eq_univ_of_forall fun y => h ⟨y, rfl⟩⟩`. Use `haveI := isIso_of_isClosedImmersion_of_surjective (pullback.snd i a)`. Conclude with `⟨inv (pullback.snd i a) ≫ pullback.fst i a, by`.

Rewrite using `[Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩`.
-/
theorem exists_lift_of_isReduced_of_range_subset {Y X Z : Scheme.{0}} [IsReduced Y] (i : Z ⟶ X)
    [IsClosedImmersion i] (a : Y ⟶ X) (h : Set.range a ⊆ Set.range i) :
    ∃ b : Y ⟶ Z, b ≫ i = a := by
  haveI : Surjective (pullback.snd i a) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun y => h ⟨y, rfl⟩⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.snd i a)
  exact ⟨inv (pullback.snd i a) ≫ pullback.fst i a, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

/- English proof (translation)
Establish `h` using `hn.map ((Scheme.ΓSpecIso (.of Ω)).hom.hom.comp t.appTop.hom)`. Rewrite `h` using `[map_natCast]`. Conclude with `h.ne_zero`.
-/
theorem natCast_ne_zero_of_isUnit_of_fieldPoint {S : Scheme.{0}} {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (Ω : Type) [Field Ω] (t : Sp Ω ⟶ S) : (n : Ω) ≠ 0 := by
  have h := hn.map ((Scheme.ΓSpecIso (.of Ω)).hom.hom.comp t.appTop.hom)
  rw [map_natCast] at h
  exact h.ne_zero

/- English proof (translation)
Introduce `hab S G G' Ga _ _ _ io n hG' hio hcl hp hn htors Ω _ _ t`. It suffices to establish `H : Finite {x : Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ t) ⟶ Ga // x ≫ io ≫ fst G G' = 1} by`. Establish `e : (𝟙_ (Over (Sp Ω))).hom ≫ t = t` using `Category.id_comp t`. Rewrite `H` using `[e]`. Then use the resulting hypothesis. Use `haveI := hG'.comm`.

Use `haveI := hG'.smooth`. Use `haveI := hG'.quasiCompact`. Establish `h` using `isGrpPullback_pullback G' t`. Set `T : Over S` to `Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ t)`. Set `ρ : (𝟙_ (Over (Sp Ω)) ⟶ (Over.pullback t).obj G') →* (T ⟶ G')` to `pushHom h _`.

Establish `hρ : ∀ y, (ρ y).left = y.left ≫ pullback.fst G'.hom t` using `fun y => rfl`. Establish `hinj : Function.Injective ρ` using `fun y z hyz => by ext1`. Use `pullback.hom_ext ?_ ((Over.w y).trans (Over.w z).symm)` and prove the remaining obligations. Rewrite using `[← hρ, ← hρ, hyz]`. Establish `hsurj : Function.Surjective ρ` using `fun x => ⟨Over.homMk (pullback.lift x.left (𝟙_ (Over (Sp Ω))).hom (Over.w x)) (pullback.lift_snd _ _ _), Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩`.

Set `s : G' ⟶ G ⊗ G'` to `lift 1 (𝟙 G')`. Establish `hs₁ : ∀ y : T ⟶ G', (y ≫ s) ≫ fst G G' = 1` using `fun y => by`. Rewrite using `[Category.assoc, lift_fst, MonObj.comp_one]`. Establish `hs₂ : ∀ y : T ⟶ G', (y ≫ s) ≫ snd G G' = y` using `fun y => by`. Rewrite using `[Category.assoc, lift_snd, Category.comp_id]`.

Set `σ : (T ⟶ G') →* (T ⟶ G ⊗ G')` to `MonoidHom.mk' (fun y => y ≫ s) fun y z => by`. Use `CartesianMonoidalCategory.hom_ext _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[hs₁, MonObj.mul_comp, hs₁, hs₁, _root_.mul_one]`. Rewrite using `[hs₂, MonObj.mul_comp, hs₂, hs₂]`. Set `κ : (T ⟶ Ga) →* (T ⟶ G ⊗ G')` to `MonoidHom.mk' (fun x => x ≫ io) fun x y => MonObj.mul_comp x y io`.

Use `haveI : Mono io := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono io.left))`. Establish `hκ : Function.Injective κ` using `fun x y hxy => (cancel_mono io).1 hxy`. Set `C` to `κ.range.comap (σ.comp ρ)`. Establish `hC : Finite C`. Use `finite_of_isClosed_torusExtension_of_pow_eq_one hab Ω ((Over.pullback t).obj G') n (inferInstanceAs (LocallyOfFiniteType (pullback.snd G'.hom t))) (inferInstanceAs (QuasiCompact (pullback.snd G'.hom t))) (hG'.fibres Ω t) hp (natCast_ne_zero_of_isUnit_of_fieldPoint hn Ω t) C ((pul …` and prove the remaining obligations.

Introduce and unpack `⟨x, hx⟩ _ ⟨p, rfl⟩`. Establish `e : x.left ≫ io.left = y.left ≫ pullback.fst G'.hom t ≫ s.left` using `(congrArg (fun z => z.left) hx).trans (Category.assoc _ _ _)`. Conclude with `⟨x.left p, by rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]⟩`. Use `haveI : IsReduced T.left := inferInstanceAs (IsReduced (Sp Ω))`. Take `⟨b, hb⟩` from `exists_lift_of_isReduced_of_range_subset io.left (ρ y ≫ s).left (by`.

Introduce and unpack `_ ⟨p, rfl⟩`. Establish `e : (ρ y ≫ s).left = y.left ≫ pullback.fst G'.hom t ≫ s.left` using `Category.assoc _ _ _`. Rewrite using `[e, Scheme.Hom.comp_apply]`. Conclude with `hy ⟨p, rfl⟩)`. Conclude with `⟨Over.homMk b (by rw [← Over.w io, ← Category.assoc, hb, Over.w]), Over.OverMorphism.ext hb⟩`.

Introduce and unpack `y ⟨x, hx⟩ hy`. Establish `hx1 : x = 1`. Use `htors T x (hκ ?_) ?_` and prove the remaining obligations. Rewrite using `[map_pow, hx, ← map_pow, hy, map_one, map_one]`. Rewrite using `[← Category.assoc]`.

Conclude with `(congrArg (· ≫ fst G G') hx).trans (hs₁ _)`. Use `hinj ?_` and prove the remaining obligations. Rewrite using `[map_one, ← hs₂ (ρ y)]`. Establish `e : ρ y ≫ s = 1` using `hx.symm.trans (by rw [hx1, map_one])`. Rewrite using `[e, MonObj.one_comp]`.

Use `choose r hr using hsurj`. Establish `key : ∀ x : {x : T ⟶ Ga // x ≫ io ≫ fst G G' = 1}, κ x.1 = σ (ρ (r (x.1 ≫ io ≫ snd G G')))` using `fun x => by`. Rewrite using `[hr]`. Use `CartesianMonoidalCategory.hom_ext _ _ ?_ ?_` and prove the remaining obligations. Conclude with `((Category.assoc _ _ _).trans x.2).trans (hs₁ _).symm`.

Conclude with `(Category.assoc _ _ _).trans (hs₂ _).symm`. Use `Finite.of_injective (fun x : {x : T ⟶ Ga // x ≫ io ≫ fst G G' = 1} => (⟨r (x.1 ≫ io ≫ snd G G'), x.1, key x⟩ : C)) fun x y hxy => Subtype.ext (hκ ?_)` and prove the remaining obligations. Rewrite using `[key x, key y, show r (x.1 ≫ io ≫ snd G G') = r (y.1 ≫ io ≫ snd G G') from congrArg Subtype.val hxy]`.
-/
theorem finite_geometric_kernel_of_pow_eq_one :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) → ∀ (S : Scheme.{0}) (G G' Ga : Over S) [GrpObj G] [GrpObj G'] [GrpObj Ga] (io : Ga ⟶ G ⊗ G') (n : ℕ), IsSemiAbelian G' → IsMonHom io → IsClosedImmersion io.left → n.Prime → IsUnit (n : Γ(S, ⊤)) → (∀ (Y : Over S) (x : Y ⟶ Ga), x ^ n = 1 → x ≫ io ≫ fst G G' = 1 → x = 1) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), Finite {x : Over.mk t ⟶ Ga // x ≫ io ≫ fst G G' = 1} := by
  intro hab S G G' Ga _ _ _ io n hG' hio hcl hp hn htors Ω _ _ t
  suffices H : Finite {x : Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ t) ⟶ Ga //
      x ≫ io ≫ fst G G' = 1} by
    have e : (𝟙_ (Over (Sp Ω))).hom ≫ t = t := Category.id_comp t
    rwa [e] at H
  haveI := hG'.comm
  haveI := hG'.smooth
  haveI := hG'.quasiCompact
  have h := isGrpPullback_pullback G' t
  let T : Over S := Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ t)
  let ρ : (𝟙_ (Over (Sp Ω)) ⟶ (Over.pullback t).obj G') →* (T ⟶ G') := pushHom h _
  have hρ : ∀ y, (ρ y).left = y.left ≫ pullback.fst G'.hom t := fun y => rfl
  have hinj : Function.Injective ρ := fun y z hyz => by
    ext1
    refine pullback.hom_ext ?_ ((Over.w y).trans (Over.w z).symm)
    rw [← hρ, ← hρ, hyz]
  have hsurj : Function.Surjective ρ := fun x =>
    ⟨Over.homMk (pullback.lift x.left (𝟙_ (Over (Sp Ω))).hom (Over.w x)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  let s : G' ⟶ G ⊗ G' := lift 1 (𝟙 G')
  have hs₁ : ∀ y : T ⟶ G', (y ≫ s) ≫ fst G G' = 1 := fun y => by
    rw [Category.assoc, lift_fst, MonObj.comp_one]
  have hs₂ : ∀ y : T ⟶ G', (y ≫ s) ≫ snd G G' = y := fun y => by
    rw [Category.assoc, lift_snd, Category.comp_id]
  let σ : (T ⟶ G') →* (T ⟶ G ⊗ G') := MonoidHom.mk' (fun y => y ≫ s) fun y z => by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [hs₁, MonObj.mul_comp, hs₁, hs₁, _root_.mul_one]
    · rw [hs₂, MonObj.mul_comp, hs₂, hs₂]
  let κ : (T ⟶ Ga) →* (T ⟶ G ⊗ G') :=
    MonoidHom.mk' (fun x => x ≫ io) fun x y => MonObj.mul_comp x y io
  haveI : Mono io := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono io.left))
  have hκ : Function.Injective κ := fun x y hxy => (cancel_mono io).1 hxy
  let C := κ.range.comap (σ.comp ρ)
  have hC : Finite C := by
    refine finite_of_isClosed_torusExtension_of_pow_eq_one hab Ω ((Over.pullback t).obj G') n
      (inferInstanceAs (LocallyOfFiniteType (pullback.snd G'.hom t)))
      (inferInstanceAs (QuasiCompact (pullback.snd G'.hom t))) (hG'.fibres Ω t) hp
      (natCast_ne_zero_of_isUnit_of_fieldPoint hn Ω t) C
      ((pullback.fst G'.hom t ≫ s.left) ⁻¹' Set.range io.left)
      (io.left.isClosedEmbedding.isClosed_range.preimage
        (pullback.fst G'.hom t ≫ s.left).continuous) (fun y => ⟨?_, fun hy => ?_⟩) ?_
    · rintro ⟨x, hx⟩ _ ⟨p, rfl⟩
      have e : x.left ≫ io.left = y.left ≫ pullback.fst G'.hom t ≫ s.left :=
        (congrArg (fun z => z.left) hx).trans (Category.assoc _ _ _)
      exact ⟨x.left p, by rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]⟩
    · haveI : IsReduced T.left := inferInstanceAs (IsReduced (Sp Ω))
      obtain ⟨b, hb⟩ := exists_lift_of_isReduced_of_range_subset io.left (ρ y ≫ s).left (by
        rintro _ ⟨p, rfl⟩
        have e : (ρ y ≫ s).left = y.left ≫ pullback.fst G'.hom t ≫ s.left := Category.assoc _ _ _
        rw [e, Scheme.Hom.comp_apply]
        exact hy ⟨p, rfl⟩)
      exact ⟨Over.homMk b (by rw [← Over.w io, ← Category.assoc, hb, Over.w]),
        Over.OverMorphism.ext hb⟩
    · rintro y ⟨x, hx⟩ hy
      have hx1 : x = 1 := by
        refine htors T x (hκ ?_) ?_
        · rw [map_pow, hx, ← map_pow, hy, map_one, map_one]
        · rw [← Category.assoc]
          exact (congrArg (· ≫ fst G G') hx).trans (hs₁ _)
      refine hinj ?_
      rw [map_one, ← hs₂ (ρ y)]
      have e : ρ y ≫ s = 1 := hx.symm.trans (by rw [hx1, map_one])
      rw [e, MonObj.one_comp]
  choose r hr using hsurj
  have key : ∀ x : {x : T ⟶ Ga // x ≫ io ≫ fst G G' = 1},
      κ x.1 = σ (ρ (r (x.1 ≫ io ≫ snd G G'))) := fun x => by
    rw [hr]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · exact ((Category.assoc _ _ _).trans x.2).trans (hs₁ _).symm
    · exact (Category.assoc _ _ _).trans (hs₂ _).symm
  refine Finite.of_injective (fun x : {x : T ⟶ Ga // x ≫ io ≫ fst G G' = 1} =>
    (⟨r (x.1 ≫ io ≫ snd G G'), x.1, key x⟩ : C)) fun x y hxy => Subtype.ext (hκ ?_)
  rw [key x, key y, show r (x.1 ≫ io ≫ snd G G') = r (y.1 ≫ io ≫ snd G G') from
    congrArg Subtype.val hxy]

end GlobalTheory
