import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
open IsLocalRing

namespace GlobalTheory.StrictHensUnion

open CategoryTheory Limits in

/- English proof (translation)
Introduce `R S _ _ _ ι _ _ _ D hmono hcov hD`. Establish `hp : RingHom.toMorphismProperty @RingHom.Etale ≤ MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0}`. Introduce `X Y f hf`. Use `CommRingCat.isFinitelyPresentable_hom f ?_` and prove the remaining obligations. Use `letI := f.hom.toAlgebra`.

Use `haveI : Algebra.Etale X Y := hf`. Conclude with `RingHom.finitePresentation_algebraMap.2 inferInstance`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale`. Rewrite using `[← MorphismProperty.ind_ind hp]`. Use `haveI : IsFiltered ι := inferInstance`.

Set `F : ι ⥤ CommRingCat.{0}` to `{ obj := fun i => CommRingCat.of (D i) map := fun {i j} h => CommRingCat.ofHom (Subalgebra.inclusion (hmono (leOfHom h))).toRingHom map_id := fun _ => rfl map_comp := fun _ _ => rfl }`. Set `t : (Functor.const ι).obj (CommRingCat.of R) ⟶ F` to `{ app := fun i => CommRingCat.ofHom (algebraMap R (D i)), naturality := fun _ _ _ => rfl }`. Set `s : F ⟶ (Functor.const ι).obj (CommRingCat.of S)` to `{ app := fun i => CommRingCat.ofHom (D i).val.toRingHom, naturality := fun _ _ _ => rfl }`. Use `⟨ι, inferInstance, inferInstance, F, t, s, ?_, fun i => ⟨hD i, rfl⟩⟩` and prove the remaining obligations. Use `haveI : ReflectsColimit F (forget CommRingCat.{0}) := reflectsColimit_of_reflectsIsomorphisms _ _`.

Use `isColimitOfReflects (forget CommRingCat.{0}) ?_` and prove the remaining obligations. Use `Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i x y hxy => ?_)` and prove the remaining obligations. Take `⟨i, hi⟩` from `hcov x`. Conclude with `⟨i, ⟨x, hi⟩, rfl⟩`. Establish `: x = y` using `Subtype.ext hxy`.

Conclude with `⟨i, 𝟙 i, by rw [this]⟩`.
-/
theorem indEtale_of_directed_union : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (D : ι → Subalgebra R S), Monotone D → (∀ s : S, ∃ i, s ∈ D i) → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R (D i))) → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R S) := by
  intro R S _ _ _ ι _ _ _ D hmono hcov hD
  have hp : RingHom.toMorphismProperty @RingHom.Etale ≤
      MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0} := by
    intro X Y f hf
    refine CommRingCat.isFinitelyPresentable_hom f ?_
    letI := f.hom.toAlgebra
    haveI : Algebra.Etale X Y := hf
    exact RingHom.finitePresentation_algebraMap.2 inferInstance
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
  rw [← MorphismProperty.ind_ind hp]
  haveI : IsFiltered ι := inferInstance
  let F : ι ⥤ CommRingCat.{0} :=
    { obj := fun i => CommRingCat.of (D i)
      map := fun {i j} h => CommRingCat.ofHom
        (Subalgebra.inclusion (hmono (leOfHom h))).toRingHom
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  let t : (Functor.const ι).obj (CommRingCat.of R) ⟶ F :=
    { app := fun i => CommRingCat.ofHom (algebraMap R (D i)), naturality := fun _ _ _ => rfl }
  let s : F ⟶ (Functor.const ι).obj (CommRingCat.of S) :=
    { app := fun i => CommRingCat.ofHom (D i).val.toRingHom, naturality := fun _ _ _ => rfl }
  refine ⟨ι, inferInstance, inferInstance, F, t, s, ?_, fun i => ⟨hD i, rfl⟩⟩
  haveI : ReflectsColimit F (forget CommRingCat.{0}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{0}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i x y hxy => ?_)
  · obtain ⟨i, hi⟩ := hcov x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  · have : x = y := Subtype.ext hxy
    exact ⟨i, 𝟙 i, by rw [this]⟩

def DivIdx {A : Type} [CommRing A] (M : Submonoid A) : Type := M

def DivIdx.el {A : Type} [CommRing A] {M : Submonoid A} (x : DivIdx M) : A := ((show M from x) : A)

/- English proof (translation)
The claim follows from `(show M from x).2`.
-/
theorem DivIdx.el_mem {A : Type} [CommRing A] {M : Submonoid A} (x : DivIdx M) : x.el ∈ M :=
  (show M from x).2

instance DivIdx.instPreorder {A : Type} [CommRing A] (M : Submonoid A) : Preorder (DivIdx M) where
  le x y := x.el ∣ y.el
  le_refl x := dvd_refl _
  le_trans _ _ _ h₁ h₂ := dvd_trans h₁ h₂

instance DivIdx.instIsDirected {A : Type} [CommRing A] (M : Submonoid A) :
    IsDirected (DivIdx M) (· ≤ ·) :=
  ⟨fun x y => ⟨(show M from ((show M from x) * (show M from y))), dvd_mul_right x.el y.el, dvd_mul_left y.el x.el⟩⟩

instance DivIdx.instNonempty {A : Type} [CommRing A] (M : Submonoid A) : Nonempty (DivIdx M) :=
  ⟨(1 : M)⟩

open CategoryTheory Limits in

/- English proof (translation)
Introduce `R A _ _ _ _ M`. Use `haveI : IsFiltered (DivIdx M) := inferInstance`. Establish `hunit : ∀ {x y : DivIdx M}, x ≤ y → IsUnit (algebraMap A (Localization.Away y.el) x.el)`. Introduce `x y h`. Take `⟨c, hc⟩` from `h`.

Establish `hy` using `IsLocalization.Away.algebraMap_isUnit (S := Localization.Away y.el) y.el`. Establish `he : algebraMap A (Localization.Away y.el) y.el = algebraMap A (Localization.Away y.el) x.el * algebraMap A (Localization.Away y.el) c`. Rewrite using `[← map_mul, ← hc]`. Conclude with `isUnit_of_mul_isUnit_left (he ▸ hy)`. Establish `hM : ∀ x : DivIdx M, IsUnit (algebraMap A (Localization M) x.el)` using `fun x => IsLocalization.map_units (Localization M) (⟨x.el, x.el_mem⟩ : M)`.

Set `F : DivIdx M ⥤ CommRingCat.{0}` to `{ obj := fun x => CommRingCat.of (Localization.Away x.el) map := fun {x y} h => CommRingCat.ofHom (IsLocalization.Away.lift x.el (hunit (leOfHom h))) map_id := fun x => by ext1`. Apply `IsLocalization.ringHom_ext (Submonoid.powers x.el)` to reduce the goal to its premises. Use extensionality with `a`. Simplify using `[IsLocalization.Away.lift_comp]`. Use `map_comp := fun {x y z} f g => by ext1`.

Apply `IsLocalization.ringHom_ext (Submonoid.powers x.el)` to reduce the goal to its premises. Use extensionality with `a`. Simplify using `[IsLocalization.Away.lift, IsLocalization.lift_eq] }`. Set `t : (Functor.const (DivIdx M)).obj (CommRingCat.of R) ⟶ F` to `{ app := fun x => CommRingCat.ofHom (algebraMap R (Localization.Away x.el)) naturality := fun x y h => by`. Use extensionality with `r`.

Simplify using `[F, IsScalarTower.algebraMap_apply R A (Localization.Away x.el), IsScalarTower.algebraMap_apply R A (Localization.Away y.el), IsLocalization.Away.lift, IsLocalization.lift_eq] }`. Set `s : F ⟶ (Functor.const (DivIdx M)).obj (CommRingCat.of (Localization M))` to `{ app := fun x => CommRingCat.ofHom (IsLocalization.Away.lift x.el (hM x)) naturality := fun x y h => by ext1`. Apply `IsLocalization.ringHom_ext (Submonoid.powers x.el)` to reduce the goal to its premises. Use extensionality with `a`. Simplify using `[F, IsLocalization.Away.lift, IsLocalization.lift_eq] }`.

Use `⟨DivIdx M, inferInstance, inferInstance, F, t, s, ?_, fun x => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `haveI : ReflectsColimit F (forget CommRingCat.{0}) := reflectsColimit_of_reflectsIsomorphisms _ _`. Use `isColimitOfReflects (forget CommRingCat.{0}) ?_` and prove the remaining obligations. Use `Types.FilteredColimit.isColimitOf' _ _ (fun z => ?_) (fun x u v huv => ?_)` and prove the remaining obligations. Take `⟨⟨a, m⟩, hz⟩` from `IsLocalization.mk'_surjective M (show Localization M from z)`.

Set `mi : DivIdx M` to `(show DivIdx M from m)`. Establish `hmi : mi.el = (m : A)` using `rfl`. Use `⟨mi, (algebraMap A (Localization.Away mi.el) a * IsLocalization.Away.invSelf (S := Localization.Away mi.el) mi.el : Localization.Away mi.el), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(show Localization M from z) = IsLocalization.Away.lift mi.el (hM mi) (algebraMap A (Localization.Away mi.el) a * IsLocalization.Away.invSelf mi.el)`. Establish `h1 : ∀ b : A, IsLocalization.Away.lift mi.el (hM mi) (algebraMap A (Localization.Away mi.el) b) = algebraMap A (Localization M) b`.

Introduce `b`. Simplify using `[IsLocalization.Away.lift, IsLocalization.lift_eq]`. Rewrite using `[← hz, IsLocalization.mk'_eq_iff_eq_mul, ← hmi, ← h1 mi.el, ← h1 a, ← map_mul, mul_assoc, mul_comm (IsLocalization.Away.invSelf mi.el), IsLocalization.Away.mul_invSelf, mul_one]`. Set `u' : Localization.Away x.el` to `u`. Set `v' : Localization.Away x.el` to `v`.

Set `φx : Localization.Away x.el →+* Localization M` to `IsLocalization.Away.lift x.el (hM x)`. Establish `huv' : φx (u' - v') = 0`. Rewrite using `[map_sub]`. Conclude with `sub_eq_zero.2 huv`. Take `⟨⟨a, p⟩, hw0⟩` from `IsLocalization.mk'_surjective (Submonoid.powers x.el) (u' - v')`.

Establish `hw : IsLocalization.mk' (Localization.Away x.el) a p = u' - v'` using `hw0`. Establish `ha : algebraMap A (Localization M) a = 0`. Establish `h2` using `IsLocalization.mk'_spec (Localization.Away x.el) a p`. Establish `h3` using `congrArg φx h2`. Rewrite `h3` using `[map_mul, hw, huv', zero_mul]`.

Rewrite using `[h3]`. Simplify using `[φx, IsLocalization.Away.lift, IsLocalization.lift_eq]`. Take `⟨m, hm⟩` from `(IsLocalization.map_eq_zero_iff M (Localization M) a).1 ha`. Set `k : DivIdx M` to `(show DivIdx M from ((show M from x) * m))`. Establish `hk : k.el = x.el * (m : A)` using `rfl`.

Establish `hxk : x ≤ k` using `⟨(m : A), hk⟩`. Use `⟨k, homOfLE hxk, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsLocalization.Away.lift x.el (hunit hxk) u' = IsLocalization.Away.lift x.el (hunit hxk) v'`. Rewrite using `[← sub_eq_zero, ← map_sub, ← hw]`. Establish `hmk : IsUnit (algebraMap A (Localization.Away k.el) (m : A))`.

Establish `hy` using `IsLocalization.Away.algebraMap_isUnit (S := Localization.Away k.el) k.el`. Rewrite `hy` using `[hk, map_mul]`. Conclude with `isUnit_of_mul_isUnit_right hy`. Establish `hak : algebraMap A (Localization.Away k.el) a = 0`. Apply `(hmk.mul_right_eq_zero).1` to reduce the goal to its premises.

Rewrite using `[← map_mul, hm, map_zero]`. Establish `hpk : IsUnit (IsLocalization.Away.lift x.el (hunit hxk) (algebraMap A (Localization.Away x.el) (p : A)))`. Take `⟨n, hn⟩` from `p.2`. Rewrite using `[← hn, map_pow, map_pow]`. Conclude with `((IsLocalization.Away.algebraMap_isUnit x.el).map _).pow n`.

Apply `(hpk.mul_left_eq_zero).1` to reduce the goal to its premises. Rewrite using `[← map_mul, IsLocalization.mk'_spec]`. Simplify using `[IsLocalization.Away.lift, IsLocalization.lift_eq, hak]`. Use `haveI : Algebra.Etale A (Localization.Away x.el) := Algebra.Etale.of_isLocalizationAway x.el haveI : Algebra.Etale R (Localization.Away x.el) := Algebra.Etale.comp R A _`. Express the relevant statement in the definitionally equal form `RingHom.Etale (algebraMap R (Localization.Away x.el))`.

Conclude with `RingHom.etale_algebraMap.2 inferInstance`. Use extensionality with `r`. Simplify using `[t, s, IsScalarTower.algebraMap_apply R A (Localization.Away x.el), IsScalarTower.algebraMap_apply R A (Localization M), IsLocalization.Away.lift]`. Conclude with `IsLocalization.lift_eq _ _`.
-/
theorem indEtale_localization_of_etale : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Etale R A] (M : Submonoid A), GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R (Localization M)) := by
  intro R A _ _ _ _ M
  haveI : IsFiltered (DivIdx M) := inferInstance
  have hunit : ∀ {x y : DivIdx M}, x ≤ y →
      IsUnit (algebraMap A (Localization.Away y.el) x.el) := by
    intro x y h
    obtain ⟨c, hc⟩ := h
    have hy := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away y.el) y.el
    have he : algebraMap A (Localization.Away y.el) y.el =
        algebraMap A (Localization.Away y.el) x.el * algebraMap A (Localization.Away y.el) c := by
      rw [← map_mul, ← hc]
    exact isUnit_of_mul_isUnit_left (he ▸ hy)
  have hM : ∀ x : DivIdx M, IsUnit (algebraMap A (Localization M) x.el) :=
    fun x => IsLocalization.map_units (Localization M) (⟨x.el, x.el_mem⟩ : M)
  let F : DivIdx M ⥤ CommRingCat.{0} :=
    { obj := fun x => CommRingCat.of (Localization.Away x.el)
      map := fun {x y} h => CommRingCat.ofHom (IsLocalization.Away.lift x.el (hunit (leOfHom h)))
      map_id := fun x => by
        ext1
        apply IsLocalization.ringHom_ext (Submonoid.powers x.el)
        ext a
        simp [IsLocalization.Away.lift_comp]
      map_comp := fun {x y z} f g => by
        ext1
        apply IsLocalization.ringHom_ext (Submonoid.powers x.el)
        ext a
        simp [IsLocalization.Away.lift, IsLocalization.lift_eq] }
  let t : (Functor.const (DivIdx M)).obj (CommRingCat.of R) ⟶ F :=
    { app := fun x => CommRingCat.ofHom (algebraMap R (Localization.Away x.el))
      naturality := fun x y h => by
        ext r
        simp [F, IsScalarTower.algebraMap_apply R A (Localization.Away x.el),
          IsScalarTower.algebraMap_apply R A (Localization.Away y.el),
          IsLocalization.Away.lift, IsLocalization.lift_eq] }
  let s : F ⟶ (Functor.const (DivIdx M)).obj (CommRingCat.of (Localization M)) :=
    { app := fun x => CommRingCat.ofHom (IsLocalization.Away.lift x.el (hM x))
      naturality := fun x y h => by
        ext1
        apply IsLocalization.ringHom_ext (Submonoid.powers x.el)
        ext a
        simp [F, IsLocalization.Away.lift, IsLocalization.lift_eq] }
  refine ⟨DivIdx M, inferInstance, inferInstance, F, t, s, ?_, fun x => ⟨?_, ?_⟩⟩
  · haveI : ReflectsColimit F (forget CommRingCat.{0}) :=
      reflectsColimit_of_reflectsIsomorphisms _ _
    refine isColimitOfReflects (forget CommRingCat.{0}) ?_
    refine Types.FilteredColimit.isColimitOf' _ _ (fun z => ?_) (fun x u v huv => ?_)
    · obtain ⟨⟨a, m⟩, hz⟩ := IsLocalization.mk'_surjective M (show Localization M from z)
      let mi : DivIdx M := (show DivIdx M from m)
      have hmi : mi.el = (m : A) := rfl
      refine ⟨mi, (algebraMap A (Localization.Away mi.el) a *
        IsLocalization.Away.invSelf (S := Localization.Away mi.el) mi.el : Localization.Away mi.el), ?_⟩
      change (show Localization M from z) = IsLocalization.Away.lift mi.el (hM mi)
        (algebraMap A (Localization.Away mi.el) a * IsLocalization.Away.invSelf mi.el)
      have h1 : ∀ b : A, IsLocalization.Away.lift mi.el (hM mi)
          (algebraMap A (Localization.Away mi.el) b) = algebraMap A (Localization M) b := by
        intro b
        simp [IsLocalization.Away.lift, IsLocalization.lift_eq]
      rw [← hz, IsLocalization.mk'_eq_iff_eq_mul, ← hmi, ← h1 mi.el, ← h1 a, ← map_mul, mul_assoc,
        mul_comm (IsLocalization.Away.invSelf mi.el), IsLocalization.Away.mul_invSelf, mul_one]
    · let u' : Localization.Away x.el := u
      let v' : Localization.Away x.el := v
      let φx : Localization.Away x.el →+* Localization M := IsLocalization.Away.lift x.el (hM x)
      have huv' : φx (u' - v') = 0 := by
        rw [map_sub]
        exact sub_eq_zero.2 huv
      obtain ⟨⟨a, p⟩, hw0⟩ := IsLocalization.mk'_surjective (Submonoid.powers x.el) (u' - v')
      have hw : IsLocalization.mk' (Localization.Away x.el) a p = u' - v' := hw0
      have ha : algebraMap A (Localization M) a = 0 := by
        have h2 := IsLocalization.mk'_spec (Localization.Away x.el) a p
        have h3 := congrArg φx h2
        rw [map_mul, hw, huv', zero_mul] at h3
        rw [h3]
        simp [φx, IsLocalization.Away.lift, IsLocalization.lift_eq]
      obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff M (Localization M) a).1 ha
      let k : DivIdx M := (show DivIdx M from ((show M from x) * m))
      have hk : k.el = x.el * (m : A) := rfl
      have hxk : x ≤ k := ⟨(m : A), hk⟩
      refine ⟨k, homOfLE hxk, ?_⟩
      change IsLocalization.Away.lift x.el (hunit hxk) u' = IsLocalization.Away.lift x.el (hunit hxk) v'
      rw [← sub_eq_zero, ← map_sub, ← hw]
      have hmk : IsUnit (algebraMap A (Localization.Away k.el) (m : A)) := by
        have hy := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away k.el) k.el
        rw [hk, map_mul] at hy
        exact isUnit_of_mul_isUnit_right hy
      have hak : algebraMap A (Localization.Away k.el) a = 0 := by
        apply (hmk.mul_right_eq_zero).1
        rw [← map_mul, hm, map_zero]
      have hpk : IsUnit (IsLocalization.Away.lift x.el (hunit hxk)
          (algebraMap A (Localization.Away x.el) (p : A))) := by
        obtain ⟨n, hn⟩ := p.2
        rw [← hn, map_pow, map_pow]
        exact ((IsLocalization.Away.algebraMap_isUnit x.el).map _).pow n
      apply (hpk.mul_left_eq_zero).1
      rw [← map_mul, IsLocalization.mk'_spec]
      simp [IsLocalization.Away.lift, IsLocalization.lift_eq, hak]
  · haveI : Algebra.Etale A (Localization.Away x.el) :=
      Algebra.Etale.of_isLocalizationAway x.el
    haveI : Algebra.Etale R (Localization.Away x.el) :=
      Algebra.Etale.comp R A _
    change RingHom.Etale (algebraMap R (Localization.Away x.el))
    exact RingHom.etale_algebraMap.2 inferInstance
  · ext r
    simp [t, s, IsScalarTower.algebraMap_apply R A (Localization.Away x.el),
      IsScalarTower.algebraMap_apply R A (Localization M), IsLocalization.Away.lift]
    exact IsLocalization.lift_eq _ _

open CategoryTheory in

/- English proof (translation)
Introduce `R L S _ _ _ _ _ _ _ N _ hR`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid S N) S := by`. Use `IsLocalization.self ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Rewrite using `[IsScalarTower.algebraMap_apply R L S]`.

Conclude with `(IsLocalization.map_units L (⟨n, hn⟩ : N)).map (algebraMap L S)`. Use `haveI : Algebra.IsPushout R S L S := Algebra.isPushout_of_isLocalization N L S S`. Use `haveI : Algebra.IsPushout R L S S := this.symm`. Establish `sq` using `CommRingCat.isPushout_of_isPushout R L S S`. Establish `: (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange` using `RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange`.

Conclude with `MorphismProperty.of_isPushout (P := MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale)) sq hR`.
-/
theorem indEtale_over_localization : ∀ (R L S : Type) [CommRing R] [CommRing L] [CommRing S] [Algebra R L] [Algebra R S] [Algebra L S] [IsScalarTower R L S] (N : Submonoid R) [IsLocalization N L], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R S) → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap L S) := by
  intro R L S _ _ _ _ _ _ _ N _ hR
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S N) S := by
    refine IsLocalization.self ?_
    rintro _ ⟨n, hn, rfl⟩
    rw [IsScalarTower.algebraMap_apply R L S]
    exact (IsLocalization.map_units L (⟨n, hn⟩ : N)).map (algebraMap L S)
  haveI : Algebra.IsPushout R S L S := Algebra.isPushout_of_isLocalization N L S S
  haveI : Algebra.IsPushout R L S S := this.symm
  have sq := CommRingCat.isPushout_of_isPushout R L S S
  have : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale)) sq hR

/- English proof (translation)
Establish `: (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso` using `RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso`. Establish `h2` using `CategoryTheory.MorphismProperty.RespectsIso.postcomp (CategoryTheory.MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale)) (e.toRingEquiv.toCommRingCatIso.hom) (CommRingCat.ofHom (algebraMap R A)) h`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Simplify using the standard rewrite rules.
-/
theorem indEtale_of_algEquiv {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R A)) : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R B) := by
  have : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
  have h2 := CategoryTheory.MorphismProperty.RespectsIso.postcomp
    (CategoryTheory.MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale))
    (e.toRingEquiv.toCommRingCatIso.hom) (CommRingCat.ofHom (algebraMap R A)) h
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
  convert h2 using 1
  ext x
  simp

/- English proof (translation)
Introduce `T O _ _ _ _ _ _ _ _ _ hS`. Take `⟨ι, _, _, _, Si, hmono, hcov, hA⟩` from `hS`. Use `set P : Ideal (Polynomial T) := (maximalIdeal O).comap (algebraMap (Polynomial T) O) with hP`. Use `haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _`. Establish `hu : ∀ y : P.primeCompl, IsUnit (algebraMap (Polynomial T) O y)`.

Introduce `y`. Use `y.2` as an intermediate fact. Assume the negation of the conclusion as `hy`. Conclude with `this ((IsLocalRing.mem_maximalIdeal _).2 hy)`. Set `φ : Localization.AtPrime P →+* O` to `IsLocalization.lift hu`.

Establish `hφ : φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O` using `IsLocalization.lift_comp hu`. Use `⟨P, hPp, φ, hφ, inferInstance, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective P.primeCompl x`. Rewrite using `[IsLocalization.AtPrime.isUnit_mk'_iff]`.

Introduce `ha`. Establish `h1 : algebraMap (Polynomial T) O a = algebraMap (Polynomial T) O s * φ (IsLocalization.mk' _ a s)` using `(IsLocalization.lift_mk'_spec _ _ _ _).1 rfl`. Establish `h2 : IsUnit (algebraMap (Polynomial T) O a)`. Rewrite using `[h1]`. Conclude with `(hu s).mul hx`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).1 ha h2`. Use `letI : Algebra (Localization.AtPrime P) O := φ.toAlgebra haveI : IsScalarTower (Polynomial T) (Localization.AtPrime P) O := IsScalarTower.of_algebraMap_eq fun x => (congrArg (fun f => f x) hφ).symm`. Establish `hR : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Polynomial T) O)`. Use `indEtale_of_directed_union (Polynomial T) O ι Si hmono hcov fun i => ?_` and prove the remaining obligations. Take `⟨A, _, _, _, q, _, ⟨e⟩⟩` from `hA i`.

Conclude with `indEtale_of_algEquiv e (indEtale_localization_of_etale (Polynomial T) A q.primeCompl)`. Conclude with `indEtale_over_localization (Polynomial T) (Localization.AtPrime P) O P.primeCompl hR`.
-/
theorem isStrictHenselisation_of_directed_union : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O]
    [IsSepClosed (IsLocalRing.ResidueField O)],
    (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧
      ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A)
        (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) →
    ∃ (P : Ideal (Polynomial T)) (_ : P.IsPrime) (φ : Localization.AtPrime P →+* O),
      φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ := by
  intro T O _ _ _ _ _ _ _ _ _ hS
  obtain ⟨ι, _, _, _, Si, hmono, hcov, hA⟩ := hS
  set P : Ideal (Polynomial T) := (maximalIdeal O).comap (algebraMap (Polynomial T) O) with hP
  haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
  have hu : ∀ y : P.primeCompl, IsUnit (algebraMap (Polynomial T) O y) := by
    intro y
    have := y.2
    by_contra hy
    exact this ((IsLocalRing.mem_maximalIdeal _).2 hy)
  let φ : Localization.AtPrime P →+* O := IsLocalization.lift hu
  have hφ : φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O :=
    IsLocalization.lift_comp hu
  refine ⟨P, hPp, φ, hφ, inferInstance, inferInstance, ?_, ?_⟩
  · refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    intro ha
    have h1 : algebraMap (Polynomial T) O a =
        algebraMap (Polynomial T) O s * φ (IsLocalization.mk' _ a s) :=
      (IsLocalization.lift_mk'_spec _ _ _ _).1 rfl
    have h2 : IsUnit (algebraMap (Polynomial T) O a) := by
      rw [h1]; exact (hu s).mul hx
    exact (IsLocalRing.mem_maximalIdeal _).1 ha h2
  · letI : Algebra (Localization.AtPrime P) O := φ.toAlgebra
    haveI : IsScalarTower (Polynomial T) (Localization.AtPrime P) O :=
      IsScalarTower.of_algebraMap_eq fun x => (congrArg (fun f => f x) hφ).symm
    have hR : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Polynomial T) O) := by
      refine indEtale_of_directed_union (Polynomial T) O ι Si hmono hcov fun i => ?_
      obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hA i
      exact indEtale_of_algEquiv e (indEtale_localization_of_etale (Polynomial T) A q.primeCompl)
    exact indEtale_over_localization (Polynomial T) (Localization.AtPrime P) O P.primeCompl hR

end GlobalTheory.StrictHensUnion
