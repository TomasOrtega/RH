import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

/- English proof (translation)
Establish `hmap : ∀ a : R, algebraMap R (Localization.Away (algebraMap R R' f)) a = algebraMap R' (Localization.Away (algebraMap R R' f)) (algebraMap R R' a)` using `fun a => IsScalarTower.algebraMap_apply R R' _ a`. Use `(isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨_, n, rfl⟩`. Rewrite using `[hmap, map_pow, map_pow]`. Conclude with `IsUnit.pow n (IsLocalization.Away.algebraMap_isUnit (algebraMap R R' f))`.

Introduce `z`. Take `⟨⟨r', ⟨_, n, rfl⟩⟩, hz⟩` from `IsLocalization.surj (Submonoid.powers (algebraMap R R' f)) z`. Take `⟨y, -, hy⟩` from `hc f hf r'`. Use `⟨⟨y, ⟨f ^ (n + 1), n + 1, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Simplify using `only at hz ⊢`.

Rewrite using `[hmap, hmap, hy, map_pow, map_pow, pow_succ, map_mul, ← hz, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Introduce `a b h`. Rewrite `h` using `[hmap, hmap]`. Take `⟨⟨_, k, rfl⟩, hk⟩` from `IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap R R' f)) h`.

Use `⟨⟨f ^ k, k, rfl⟩, hinj ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_pow] at hk ⊢`. Conclude with `hk`.
-/
theorem isLocalization_away_of_absorb {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R')) (c : Ideal R)
    (hc : ∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) {f : R} (hf : f ∈ c) :
    IsLocalization.Away f (Localization.Away (algebraMap R R' f)) := by
  have hmap : ∀ a : R, algebraMap R (Localization.Away (algebraMap R R' f)) a =
      algebraMap R' (Localization.Away (algebraMap R R' f)) (algebraMap R R' a) := fun a =>
    IsScalarTower.algebraMap_apply R R' _ a
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [hmap, map_pow, map_pow]
    exact IsUnit.pow n (IsLocalization.Away.algebraMap_isUnit (algebraMap R R' f))
  · intro z
    obtain ⟨⟨r', ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R R' f)) z
    obtain ⟨y, -, hy⟩ := hc f hf r'
    refine ⟨⟨y, ⟨f ^ (n + 1), n + 1, rfl⟩⟩, ?_⟩
    simp only at hz ⊢
    rw [hmap, hmap, hy, map_pow, map_pow, pow_succ, map_mul, ← hz, map_pow]
    ring
  · intro a b h
    rw [hmap, hmap] at h
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap R R' f)) h
    refine ⟨⟨f ^ k, k, rfl⟩, hinj ?_⟩
    simp only [map_mul, map_pow] at hk ⊢
    exact hk

/- English proof (translation)
Introduce `R _ R' _ _ hinj c hc g B' C Y b' e i q hsm x hx`. Choose the witnesses or unpack the hypotheses as in `⟨f, hfc, hfx⟩ : ∃ f ∈ c, f ∉ ((b' ≫ spMap (algebraMap R R')) x).asIdeal := by`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Apply `hx` to reduce the goal to its premises.

Establish `hr : Set.range (spMap (Ideal.Quotient.mk c)) = PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk c))` using `range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective`. Rewrite using `[hr, Ideal.mk_ker]`. Conclude with `hno`. Use `haveI : IsLocalization.Away f (Localization.Away (algebraMap R R' f)) := isLocalization_away_of_absorb hinj c hc hfc`. Set `l' : Sp (Localization.Away (algebraMap R R' f)) ⟶ Sp R'` to `spMap (algebraMap R' _)`.

Set `h : Sp (Localization.Away (algebraMap R R' f)) ⟶ Sp R` to `spMap (algebraMap R _)`. Use `haveI : IsOpenImmersion l' := IsOpenImmersion.of_isLocalization (algebraMap R R' f)`. Use `haveI : IsOpenImmersion h := IsOpenImmersion.of_isLocalization f`. Establish `hcomp : l' ≫ spMap (algebraMap R R') = h`. Simplify using `only [l', h, spMap, ← Spec.map_comp]`.

Use `congr 1`. Establish `hrange : Set.range h = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))` using `PrimeSpectrum.localization_away_comap_range _ f`. Establish `hrange' : Set.range l' = (PrimeSpectrum.basicOpen (algebraMap R R' f) : Set (PrimeSpectrum R'))` using `PrimeSpectrum.localization_away_comap_range _ _`. Set `j : pullback b' l' ⟶ B'` to `pullback.fst b' l'`. Set `u : pullback b' l' ⟶ Sp R` to `pullback.snd b' l' ≫ h`.

Establish `hju : j ≫ b' ≫ spMap (algebraMap R R') = u`. Simplify using `only [j, u, ← hcomp]`. Rewrite using `[← Category.assoc, pullback.condition, Category.assoc]`. Establish `hsmu : SmoothOfRelativeDimension g u` using `by haveI : SmoothOfRelativeDimension g (pullback.snd b' l') := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback b' l') hsm haveI : SmoothOfRelativeDimension 0 h := inferInstance`. Use `smoothOfRelativeDimension_comp g 0 (pullback.snd b' l') h` as an intermediate fact.

Simplify using `using this`. Establish `hD : ∀ t : ↥(pullback b' l'), f ∉ (u t).asIdeal` using `fun t => by`. Establish `: u t ∈ Set.range h` using `⟨pullback.snd b' l' t, rfl⟩`. Rewrite `this` using `[hrange]`. Conclude with `this`.

Establish `hEmpty : ∀ (T : Scheme.{0}) (a : T ⟶ pullback b' l') (a' : T ⟶ Sp (R ⧸ c)), a ≫ u = a' ≫ spMap (Ideal.Quotient.mk c) → IsEmpty T`. Introduce `T a a' w`. Use `⟨fun t => hD (a t) ?_⟩` and prove the remaining obligations. Establish `e1 : u (a t) = spMap (Ideal.Quotient.mk c) (a' t)`. Rewrite using `[← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]`.

Rewrite using `[e1]`. Use `show Ideal.Quotient.mk c f ∈ (a' t).asIdeal`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 hfc]`. Conclude with `Ideal.zero_mem _`. Establish `w1 : 𝟙 (pullback b' l') ≫ u = (j ≫ b') ≫ spMap (algebraMap R R')`.

Rewrite using `[Category.id_comp, Category.assoc, hju]`. Establish `w2 : Scheme.emptyTo (pullback b' l') ≫ u = (Scheme.emptyTo C ≫ e) ≫ spMap (Ideal.Quotient.mk c)` using `Scheme.empty_ext _ _`. Use `⟨pullback b' l', pullback b' l', ∅, u, 𝟙 _, j, Scheme.emptyTo _, Scheme.emptyTo C, hsmu, ⟨⟨w1⟩, ⟨PullbackCone.IsLimit.mk w1 (fun s => s.fst) (fun s => Category.comp_id _) (fun s => ?_) (fun s m h1 _ => by simpa using h1)⟩⟩, inferInstance, ?_, ⟨⟨w2⟩, ⟨PullbackCone.IsLimit.mk w2 (f …` and prove the remaining obligations. Establish `hr : Set.range s.snd ⊆ Set.range l'`. Introduce and unpack `_ ⟨t, rfl⟩`.

Rewrite using `[hrange']`. Establish `e1 : spMap (algebraMap R R') (s.snd t) = u (s.fst t)`. Rewrite using `[← Scheme.Hom.comp_apply, ← s.condition, Scheme.Hom.comp_apply]`. Use `hD (s.fst t)` as an intermediate fact. Rewrite `this` using `[← e1]`.

Conclude with `this`. Establish `hl : IsOpenImmersion.lift l' s.snd hr ≫ l' = s.snd` using `IsOpenImmersion.lift_fac l' s.snd hr`. Establish `hl2 : IsOpenImmersion.lift l' s.snd hr = s.fst ≫ pullback.snd b' l'`. Rewrite using `[← cancel_mono h, ← hcomp, ← Category.assoc, hl, ← s.condition]`. Use `show s.fst ≫ (pullback.snd b' l' ≫ h) = _`.

Rewrite using `[← hcomp]`. Simplify using `only [Category.assoc]`. Use `show s.fst ≫ j ≫ b' = s.snd`. Rewrite using `[← hl, hl2]`. Conclude with `congrArg (s.fst ≫ ·) pullback.condition`.

Rewrite using `[IsOpenImmersion.range_pullbackFst l' b'] show b' x ∈ Set.range l'`. Rewrite using `[hrange']`. Conclude with `hfx`. Introduce `T a a' _ haveI : IsEmpty T := ⟨fun t => isEmptyElim (a' t)⟩`. Conclude with `⟨isInitialOfIsEmpty.to Y, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _⟩`.
-/
theorem pinched_off : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), SmoothOfRelativeDimension g b' → ∀ x : B', (b' ≫ spMap (algebraMap R R')) x ∉ Set.range (spMap (Ideal.Quotient.mk c)) → GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q x := by
  intro R _ R' _ _ hinj c hc g B' C Y b' e i q hsm x hx
  obtain ⟨f, hfc, hfx⟩ : ∃ f ∈ c, f ∉ ((b' ≫ spMap (algebraMap R R')) x).asIdeal := by
    by_contra hno
    push_neg at hno
    apply hx
    have hr : Set.range (spMap (Ideal.Quotient.mk c)) =
        PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk c)) :=
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
    rw [hr, Ideal.mk_ker]
    exact hno
  haveI : IsLocalization.Away f (Localization.Away (algebraMap R R' f)) :=
    isLocalization_away_of_absorb hinj c hc hfc
  let l' : Sp (Localization.Away (algebraMap R R' f)) ⟶ Sp R' := spMap (algebraMap R' _)
  let h : Sp (Localization.Away (algebraMap R R' f)) ⟶ Sp R := spMap (algebraMap R _)
  haveI : IsOpenImmersion l' := IsOpenImmersion.of_isLocalization (algebraMap R R' f)
  haveI : IsOpenImmersion h := IsOpenImmersion.of_isLocalization f
  have hcomp : l' ≫ spMap (algebraMap R R') = h := by
    simp only [l', h, spMap, ← Spec.map_comp]
    congr 1
  have hrange : Set.range h = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range _ f
  have hrange' : Set.range l' =
      (PrimeSpectrum.basicOpen (algebraMap R R' f) : Set (PrimeSpectrum R')) :=
    PrimeSpectrum.localization_away_comap_range _ _
  let j : pullback b' l' ⟶ B' := pullback.fst b' l'
  let u : pullback b' l' ⟶ Sp R := pullback.snd b' l' ≫ h
  have hju : j ≫ b' ≫ spMap (algebraMap R R') = u := by
    simp only [j, u, ← hcomp]
    rw [← Category.assoc, pullback.condition, Category.assoc]
  have hsmu : SmoothOfRelativeDimension g u := by
    haveI : SmoothOfRelativeDimension g (pullback.snd b' l') :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback b' l') hsm
    haveI : SmoothOfRelativeDimension 0 h := inferInstance
    have := smoothOfRelativeDimension_comp g 0 (pullback.snd b' l') h
    simpa using this
  have hD : ∀ t : ↥(pullback b' l'), f ∉ (u t).asIdeal := fun t => by
    have : u t ∈ Set.range h := ⟨pullback.snd b' l' t, rfl⟩
    rw [hrange] at this
    exact this
  have hEmpty : ∀ (T : Scheme.{0}) (a : T ⟶ pullback b' l') (a' : T ⟶ Sp (R ⧸ c)),
      a ≫ u = a' ≫ spMap (Ideal.Quotient.mk c) → IsEmpty T := by
    intro T a a' w
    refine ⟨fun t => hD (a t) ?_⟩
    have e1 : u (a t) = spMap (Ideal.Quotient.mk c) (a' t) := by
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
    rw [e1]
    show Ideal.Quotient.mk c f ∈ (a' t).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hfc]
    exact Ideal.zero_mem _
  have w1 : 𝟙 (pullback b' l') ≫ u = (j ≫ b') ≫ spMap (algebraMap R R') := by
    rw [Category.id_comp, Category.assoc, hju]
  have w2 : Scheme.emptyTo (pullback b' l') ≫ u = (Scheme.emptyTo C ≫ e) ≫ spMap (Ideal.Quotient.mk c) :=
    Scheme.empty_ext _ _
  refine ⟨pullback b' l', pullback b' l', ∅, u, 𝟙 _, j, Scheme.emptyTo _, Scheme.emptyTo C, hsmu,
    ⟨⟨w1⟩, ⟨PullbackCone.IsLimit.mk w1 (fun s => s.fst) (fun s => Category.comp_id _) (fun s => ?_)
      (fun s m h1 _ => by simpa using h1)⟩⟩, inferInstance, ?_,
    ⟨⟨w2⟩, ⟨PullbackCone.IsLimit.mk w2
      (fun s => haveI := hEmpty _ _ _ s.condition; isInitialOfIsEmpty.to _)
      (fun s => by haveI := hEmpty _ _ _ s.condition; exact isInitialOfIsEmpty.hom_ext _ _)
      (fun s => by haveI := hEmpty _ _ _ s.condition; exact isInitialOfIsEmpty.hom_ext _ _)
      (fun s m _ _ => by haveI := hEmpty _ _ _ s.condition; exact isInitialOfIsEmpty.hom_ext _ _)⟩⟩, ?_⟩
  · have hr : Set.range s.snd ⊆ Set.range l' := by
      rintro _ ⟨t, rfl⟩
      rw [hrange']
      have e1 : spMap (algebraMap R R') (s.snd t) = u (s.fst t) := by
        rw [← Scheme.Hom.comp_apply, ← s.condition, Scheme.Hom.comp_apply]
      have := hD (s.fst t)
      rw [← e1] at this
      exact this
    have hl : IsOpenImmersion.lift l' s.snd hr ≫ l' = s.snd := IsOpenImmersion.lift_fac l' s.snd hr
    have hl2 : IsOpenImmersion.lift l' s.snd hr = s.fst ≫ pullback.snd b' l' := by
      rw [← cancel_mono h, ← hcomp, ← Category.assoc, hl, ← s.condition]
      show s.fst ≫ (pullback.snd b' l' ≫ h) = _
      rw [← hcomp]
      simp only [Category.assoc]
    show s.fst ≫ j ≫ b' = s.snd
    rw [← hl, hl2]
    exact congrArg (s.fst ≫ ·) pullback.condition
  · rw [IsOpenImmersion.range_pullbackFst l' b']
    show b' x ∈ Set.range l'
    rw [hrange']
    exact hfx
  · intro T a a' _
    haveI : IsEmpty T := ⟨fun t => isEmptyElim (a' t)⟩
    exact ⟨isInitialOfIsEmpty.to Y, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _⟩

end GlobalTheory.Pinch
