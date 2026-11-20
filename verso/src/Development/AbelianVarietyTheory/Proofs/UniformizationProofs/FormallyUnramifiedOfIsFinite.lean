import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FiniteOnePoint

/- English proof (translation)
Use `haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion (MorphismProperty.diagonal @IsOpenImmersion) := MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2 le_rfl`. Establish `ho : IsOpenImmersion s` using `MorphismProperty.of_postcomp (W := @IsOpenImmersion) (W' := MorphismProperty.diagonal @IsOpenImmersion) s f (inferInstanceAs (IsOpenImmersion (pullback.diagonal f))) (by rw [hs]; infer_instance)`. Use `LocallyOfFiniteType.jacobsonSpace f` as an intermediate fact. Establish `hsurj : Surjective s` using `⟨fun x => by`. Assume the negation of the conclusion as `hx`.

Take `⟨c, hc, hc'⟩` from `nonempty_inter_closedPoints (Z := (Set.range s)ᶜ) ⟨x, hx⟩ s.isOpenEmbedding.isOpen_range.isClosed_compl.isLocallyClosed`. Use `hc ⟨IsLocalRing.closedPoint K, ?_⟩` and prove the remaining obligations. Rewrite using `[← h _ (pointOfClosedPoint_comp f c hc')]`. Conclude with `pointOfClosedPoint_apply f c hc' _⟩`. Establish `: IsIso s` using `(isIso_iff_isOpenImmersion_and_surjective s).2 ⟨ho, hsurj⟩`.

Establish `: IsIso (s ≫ f)` using `by rw [hs]; infer_instance`. Conclude with `IsIso.of_isIso_comp_left s f`.
-/
theorem isIso_of_formallyUnramified {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] [FormallyUnramified f]
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (h : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → p = s) : IsIso f := by
  haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (MorphismProperty.diagonal @IsOpenImmersion) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2 le_rfl
  have ho : IsOpenImmersion s :=
    MorphismProperty.of_postcomp (W := @IsOpenImmersion)
      (W' := MorphismProperty.diagonal @IsOpenImmersion) s f
      (inferInstanceAs (IsOpenImmersion (pullback.diagonal f))) (by rw [hs]; infer_instance)
  have := LocallyOfFiniteType.jacobsonSpace f
  have hsurj : Surjective s := ⟨fun x => by
    by_contra hx
    obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints (Z := (Set.range s)ᶜ) ⟨x, hx⟩
      s.isOpenEmbedding.isOpen_range.isClosed_compl.isLocallyClosed
    refine hc ⟨IsLocalRing.closedPoint K, ?_⟩
    rw [← h _ (pointOfClosedPoint_comp f c hc')]
    exact pointOfClosedPoint_apply f c hc' _⟩
  have : IsIso s := (isIso_iff_isOpenImmersion_and_surjective s).2 ⟨ho, hsurj⟩
  have : IsIso (s ≫ f) := by rw [hs]; infer_instance
  exact IsIso.of_isIso_comp_left s f

/- English proof (translation)
Take `⟨N, hN, h⟩` from `FiniteFlatKilled.main K G hf inferInstance`. Establish `hu : IsUnit (N : Γ(Spec (CommRingCat.of K), ⊤))`. Establish `h1 : IsUnit (N : K)` using `(Nat.cast_ne_zero.2 (by omega)).isUnit`. Simplify using `using h1.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom`. Establish `h2` using `formallyUnramified_mulA _ G N hu`.

Establish `h3 : (mulA G N).left = G.hom ≫ η[G].left`. Rewrite using `[show mulA G N = 1 from h, Hom.one_def]`. Both sides reduce to the same expression. Rewrite `h2` using `[h3]`. Conclude with `FormallyUnramified.of_comp G.hom η[G].left`.
-/
theorem formallyUnramified_of_isFinite {K : Type} [Field K] [CharZero K]
    (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsCommMonObj G] (hf : IsFinite G.hom) :
    FormallyUnramified G.hom := by
  obtain ⟨N, hN, h⟩ := FiniteFlatKilled.main K G hf inferInstance
  have hu : IsUnit (N : Γ(Spec (CommRingCat.of K), ⊤)) := by
    have h1 : IsUnit (N : K) := (Nat.cast_ne_zero.2 (by omega)).isUnit
    simpa using h1.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have h2 := formallyUnramified_mulA _ G N hu
  have h3 : (mulA G N).left = G.hom ≫ η[G].left := by
    rw [show mulA G N = 1 from h, Hom.one_def]
    rfl
  rw [h3] at h2
  exact FormallyUnramified.of_comp G.hom η[G].left

/- English proof (translation)
Introduce `S B _ _ H j hj hf ⟨e, he⟩ hsub K _ _ _ t hpt T a y`. Establish `he' : ∀ T : Over S, (toUnit T ≫ e) ≫ j = 1` using `fun T => by`. Rewrite using `[Category.assoc, he, MonObj.comp_one]`. Establish `hinv : ∀ (T : Over S) (x : T ⟶ H), ∃ z : T ⟶ H, z ≫ j = (x ≫ j)⁻¹` using `fun T x => by`. Take `⟨z, hz⟩` from `hsub T (toUnit T ≫ e) x`.

Conclude with `⟨z, by rw [hz, he', _root_.one_mul]⟩`. Take `⟨i, hi⟩` from `hinv H (𝟙 H)`. Take `⟨w, hw⟩` from `hinv (H ⊗ H) (snd H H)`. Take `⟨m, hm⟩` from `hsub (H ⊗ H) (fst H H) w`. Take `⟨_, _⟩` from `ReducedSubgroup.exists_grpObj_of_mono j e m i (by rw [he, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]) (by`.

Rewrite using `[hm, hw, inv_inv, Hom.mul_def]`. Use `congr 1)`. Use the proof step `(by rw [hi, Category.id_comp, Hom.inv_def])`. Use `haveI : IsCommMonObj H := ⟨by rw [← cancel_mono j, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]⟩`. Establish `hfin : IsFinite (pullback.snd H.hom t)` using `inferInstance`.

Establish `hunr : FormallyUnramified (pullback.snd H.hom t)` using `formallyUnramified_of_isFinite ((Over.pullback t).obj H) hfin`. Establish `hiso : IsIso (pullback.snd H.hom t)`. Use `isIso_of_formallyUnramified _ (pullback.lift (toUnit (Over.mk t) ≫ e).left (𝟙 _) ((Over.w _).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _) fun p hp => ?_` and prove the remaining obligations. Set `x : Over.mk t ⟶ H` to `Over.homMk (p ≫ pullback.fst H.hom t) (by`. Express the relevant statement in the definitionally equal form `(p ≫ pullback.fst H.hom t) ≫ H.hom = t`.

Rewrite using `[Category.assoc, pullback.condition, reassoc_of% hp])`. Establish `hx : x = toUnit _ ≫ e` using `by rw [← cancel_mono j, hpt, he']`. Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[pullback.lift_fst, ← hx]`. Both sides reduce to the same expression.

Rewrite using `[pullback.lift_snd, hp]`. Establish `key : ∀ y₁ y₂ : T ⟶ H, y₁ = y₂` using `fun y₁ y₂ => by`. Establish `h : pullback.lift y₁.left a.left ((Over.w y₁).trans (Over.w a).symm) = pullback.lift (f` using `H.hom) (g := t) y₂.left a.left ((Over.w y₂).trans (Over.w a).symm) := by`. Rewrite using `[← cancel_mono (pullback.snd H.hom t)]`. Conclude with `(pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm`.

Use `ext1`. Conclude with `(pullback.lift_fst _ _ _).symm.trans ((h =≫ pullback.fst H.hom t).trans (pullback.lift_fst _ _ _))`. Rewrite using `[key y (toUnit T ≫ e), he']`.
-/
theorem main : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (H : Over S) (j : H ⟶ B), Mono j → IsFinite H.hom → (∃ y : 𝟙_ _ ⟶ H, y ≫ j = 1) → (∀ (T : Over S) (x y : T ⟶ H), ∃ z : T ⟶ H, z ≫ j = (x ≫ j) * (y ≫ j)⁻¹) → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (t : Spec (CommRingCat.of K) ⟶ S), (∀ x : Over.mk t ⟶ H, x ≫ j = 1) → ∀ (T : Over S) (_ : T ⟶ Over.mk t) (y : T ⟶ H), y ≫ j = 1 := by
  intro S B _ _ H j hj hf ⟨e, he⟩ hsub K _ _ _ t hpt T a y
  have he' : ∀ T : Over S, (toUnit T ≫ e) ≫ j = 1 := fun T => by
    rw [Category.assoc, he, MonObj.comp_one]
  have hinv : ∀ (T : Over S) (x : T ⟶ H), ∃ z : T ⟶ H, z ≫ j = (x ≫ j)⁻¹ := fun T x => by
    obtain ⟨z, hz⟩ := hsub T (toUnit T ≫ e) x
    exact ⟨z, by rw [hz, he', _root_.one_mul]⟩
  obtain ⟨i, hi⟩ := hinv H (𝟙 H)
  obtain ⟨w, hw⟩ := hinv (H ⊗ H) (snd H H)
  obtain ⟨m, hm⟩ := hsub (H ⊗ H) (fst H H) w
  obtain ⟨_, _⟩ := ReducedSubgroup.exists_grpObj_of_mono j e m i
    (by rw [he, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
    (by
      rw [hm, hw, inv_inv, Hom.mul_def]
      congr 1)
    (by rw [hi, Category.id_comp, Hom.inv_def])
  haveI : IsCommMonObj H :=
    ⟨by rw [← cancel_mono j, Category.assoc, IsMonHom.mul_hom,
      ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]⟩
  have hfin : IsFinite (pullback.snd H.hom t) := inferInstance
  have hunr : FormallyUnramified (pullback.snd H.hom t) :=
    formallyUnramified_of_isFinite ((Over.pullback t).obj H) hfin
  have hiso : IsIso (pullback.snd H.hom t) := by
    refine isIso_of_formallyUnramified _
      (pullback.lift (toUnit (Over.mk t) ≫ e).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _) fun p hp => ?_
    let x : Over.mk t ⟶ H := Over.homMk (p ≫ pullback.fst H.hom t) (by
      change (p ≫ pullback.fst H.hom t) ≫ H.hom = t
      rw [Category.assoc, pullback.condition, reassoc_of% hp])
    have hx : x = toUnit _ ≫ e := by rw [← cancel_mono j, hpt, he']
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, ← hx]
      rfl
    · rw [pullback.lift_snd, hp]
  have key : ∀ y₁ y₂ : T ⟶ H, y₁ = y₂ := fun y₁ y₂ => by
    have h : pullback.lift y₁.left a.left ((Over.w y₁).trans (Over.w a).symm) =
        pullback.lift (f := H.hom) (g := t) y₂.left a.left ((Over.w y₂).trans (Over.w a).symm) := by
      rw [← cancel_mono (pullback.snd H.hom t)]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
    ext1
    exact (pullback.lift_fst _ _ _).symm.trans
      ((h =≫ pullback.fst H.hom t).trans (pullback.lift_fst _ _ _))
  rw [key y (toUnit T ≫ e), he']

end FiniteOnePoint

end GlobalTheory
