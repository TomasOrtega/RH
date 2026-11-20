import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

universe u

section Descent

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency.types false in

/- English proof (translation)
Use `⟨fun {A X Y Z fst snd f g} h hf hfst => ?_⟩` and prove the remaining obligations. Take `⟨⟨hs, -⟩, hqc⟩` from `hf`. Establish `hsnd : Surjective snd` using `MorphismProperty.of_isPullback h hs`. Establish `: QuasiCompact f` using `hqc`. Establish `: QuasiCompact fst` using `hfst`.

Use `show QuasiCompact g`. Rewrite using `[quasiCompact_iff]`. Introduce `U hU hc`. Establish `h1 : IsCompact (fst ⁻¹' (f ⁻¹' U))` using `(quasiCompact_iff fst).1 ‹_› _ (hU.preimage f.continuous) ((quasiCompact_iff f).1 ‹_› U hU hc)`. Establish `hcond : ∀ z, f (fst z) = g (snd z)` using `fun z => by`.

Rewrite using `[← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]`. Establish `: g ⁻¹' U = snd '' (fst ⁻¹' (f ⁻¹' U))`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Take `⟨z, rfl⟩` from `hsnd.surj y`. Conclude with `⟨z, by simpa [Set.mem_preimage, hcond] using hy, rfl⟩`. Introduce and unpack `⟨z, hz, rfl⟩`. Simplify `hz` using `[Set.mem_preimage, ← hcond]`. Rewrite using `[this]`.

Conclude with `h1.image snd.continuous`.
-/
theorem _root_.GlobalTheory.quasiCompact_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@QuasiCompact : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine ⟨fun {A X Y Z fst snd f g} h hf hfst => ?_⟩
  obtain ⟨⟨hs, -⟩, hqc⟩ := hf
  have hsnd : Surjective snd := MorphismProperty.of_isPullback h hs
  have : QuasiCompact f := hqc
  have : QuasiCompact fst := hfst
  show QuasiCompact g
  rw [quasiCompact_iff]
  intro U hU hc
  have h1 : IsCompact (fst ⁻¹' (f ⁻¹' U)) :=
    (quasiCompact_iff fst).1 ‹_› _ (hU.preimage f.continuous) ((quasiCompact_iff f).1 ‹_› U hU hc)
  have hcond : ∀ z, f (fst z) = g (snd z) := fun z => by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  have : g ⁻¹' U = snd '' (fst ⁻¹' (f ⁻¹' U)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, rfl⟩ := hsnd.surj y
      exact ⟨z, by simpa [Set.mem_preimage, hcond] using hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      simpa [Set.mem_preimage, ← hcond] using hz
  rw [this]
  exact h1.image snd.continuous

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency.types false in

/- English proof (translation)
Establish `: IsZariskiLocalAtTarget (@QuasiSeparated : MorphismProperty Scheme.{u})` using `@HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat`. Use `IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ (@Surjective ⊓ @Flat) ?_ ?_` and prove the remaining obligations. Introduce and unpack `X Y f ⟨hl, hs⟩`. Conclude with `⟨hs, IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ f hl⟩`. Introduce `R S Y φ g hφ hfst`.

Take `⟨hs, -⟩` from `hφ`. Establish `: QuasiSeparated (pullback.fst (Spec.map φ) g)` using `hfst`. Establish `: QuasiSeparatedSpace ↥(Limits.pullback (Spec.map φ) g)` using `quasiSeparatedSpace_of_quasiSeparated (pullback.fst (Spec.map φ) g)`. Establish `hsnd : Surjective (pullback.snd (Spec.map φ) g)` using `MorphismProperty.pullback_snd _ _ hs`. Establish `: QuasiCompact (pullback.snd (Spec.map φ) g)` using `MorphismProperty.pullback_snd _ _ (inferInstanceAs (QuasiCompact (Spec.map φ)))`.

Use `show QuasiSeparated g`. Rewrite using `[quasiSeparated_iff_quasiSeparatedSpace]`. Use `⟨fun U V hU hUc hV hVc => ?_⟩` and prove the remaining obligations. Use `set s := pullback.snd (Spec.map φ) g`. Establish `hpre : ∀ W : Set Y, IsOpen W → IsCompact W → IsCompact (s ⁻¹' W)` using `fun W hW hWc => (quasiCompact_iff s).1 ‹_› W hW hWc`.

Establish `: U ∩ V = s '' (s ⁻¹' U ∩ s ⁻¹' V)`. Rewrite using `[← Set.preimage_inter, Set.image_preimage_eq _ hsnd.surj]`. Rewrite using `[this]`. Conclude with `(QuasiSeparatedSpace.inter_isCompact _ _ (hU.preimage s.continuous) (hpre U hU hUc) (hV.preimage s.continuous) (hpre V hV hVc)).image s.continuous`.
-/
theorem _root_.GlobalTheory.quasiSeparated_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@QuasiSeparated : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have : IsZariskiLocalAtTarget (@QuasiSeparated : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ (@Surjective ⊓ @Flat) ?_ ?_
  · rintro X Y f ⟨hl, hs⟩
    exact ⟨hs, IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ f hl⟩
  · intro R S Y φ g hφ hfst
    obtain ⟨hs, -⟩ := hφ
    have : QuasiSeparated (pullback.fst (Spec.map φ) g) := hfst
    have : QuasiSeparatedSpace ↥(Limits.pullback (Spec.map φ) g) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst (Spec.map φ) g)
    have hsnd : Surjective (pullback.snd (Spec.map φ) g) :=
      MorphismProperty.pullback_snd _ _ hs
    have : QuasiCompact (pullback.snd (Spec.map φ) g) :=
      MorphismProperty.pullback_snd _ _ (inferInstanceAs (QuasiCompact (Spec.map φ)))
    show QuasiSeparated g
    rw [quasiSeparated_iff_quasiSeparatedSpace]
    refine ⟨fun U V hU hUc hV hVc => ?_⟩
    set s := pullback.snd (Spec.map φ) g
    have hpre : ∀ W : Set Y, IsOpen W → IsCompact W → IsCompact (s ⁻¹' W) :=
      fun W hW hWc => (quasiCompact_iff s).1 ‹_› W hW hWc
    have : U ∩ V = s '' (s ⁻¹' U ∩ s ⁻¹' V) := by
      rw [← Set.preimage_inter, Set.image_preimage_eq _ hsnd.surj]
    rw [this]
    exact (QuasiSeparatedSpace.inter_isCompact _ _ (hU.preimage s.continuous) (hpre U hU hUc)
      (hV.preimage s.continuous) (hpre V hV hVc)).image s.continuous

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency.types false in

/- English proof (translation)
Establish `hQf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) f` using `⟨⟨‹Surjective f›, ‹Flat f›⟩, inferInstance⟩`. Establish `: QuasiCompact p` using `@MorphismProperty.of_isPullback_of_descendsAlong _ _ _ _ _ _ _ _ _ _ _ _ _root_.GlobalTheory.quasiCompact_descendsAlong_fpqc H.flip hQf (inferInstanceAs (QuasiCompact q))`. Establish `: QuasiSeparated p` using `@MorphismProperty.of_isPullback_of_descendsAlong _ _ _ _ _ _ _ _ _ _ _ _ _root_.GlobalTheory.quasiSeparated_descendsAlong_fpqc H.flip hQf (inferInstanceAs (QuasiSeparated q))`. Establish `hSpec : IsPullback (Spec.map g.appTop) (Spec.map q.appTop) (Spec.map p.appTop) (Spec.map f.appTop)` using `isPullback_SpecMap_of_isPushout _ _ _ _ (_root_.GlobalTheory.ProperFunctions.isPushout_appTop H)`. Establish `hfsq : IsPullback (inv T.toSpecΓ) (Spec.map f.appTop) f (inv S.toSpecΓ)` using `IsPullback.of_horiz_isIso ⟨by`.

Rewrite using `[IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, Scheme.toSpecΓ_naturality]⟩`. Establish `hQ' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (Spec.map g.appTop)` using `MorphismProperty.of_isPullback hSpec.flip (MorphismProperty.of_isPullback hfsq hQf)`. Establish `hiso : IsPullback T.toSpecΓ f (Spec.map f.appTop) S.toSpecΓ` using `IsPullback.of_horiz_isIso ⟨(Scheme.toSpecΓ_naturality f).symm⟩`. Establish `hbig : IsPullback (Y.toSpecΓ ≫ Spec.map q.appTop) g (Spec.map f.appTop) (X.toSpecΓ ≫ Spec.map p.appTop)`. Rewrite using `[← Scheme.toSpecΓ_naturality, ← Scheme.toSpecΓ_naturality]`.

Conclude with `H.flip.paste_horiz hiso`. Establish `htop : IsPullback Y.toSpecΓ g (Spec.map g.appTop) X.toSpecΓ` using `IsPullback.of_right hbig (Scheme.toSpecΓ_naturality g).symm hSpec.flip`. Establish `: MorphismProperty.isomorphisms Scheme.{u} X.toSpecΓ` using `MorphismProperty.of_isPullback_of_descendsAlong htop hQ' (MorphismProperty.isomorphisms.infer_property _)`. Conclude with `⟨this⟩`.
-/
theorem _root_.GlobalTheory.isAffine_of_isPullback_of_flat_surjective {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X}
    {p : X ⟶ S} {q : Y ⟶ T} (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat f]
    [Surjective f] [IsAffine Y] : IsAffine X := by
  have hQf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) f :=
    ⟨⟨‹Surjective f›, ‹Flat f›⟩, inferInstance⟩
  have : QuasiCompact p :=
    @MorphismProperty.of_isPullback_of_descendsAlong _ _ _ _ _ _ _ _ _ _ _ _
      _root_.GlobalTheory.quasiCompact_descendsAlong_fpqc H.flip hQf (inferInstanceAs (QuasiCompact q))
  have : QuasiSeparated p :=
    @MorphismProperty.of_isPullback_of_descendsAlong _ _ _ _ _ _ _ _ _ _ _ _
      _root_.GlobalTheory.quasiSeparated_descendsAlong_fpqc H.flip hQf (inferInstanceAs (QuasiSeparated q))
  have hSpec : IsPullback (Spec.map g.appTop) (Spec.map q.appTop) (Spec.map p.appTop)
      (Spec.map f.appTop) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (_root_.GlobalTheory.ProperFunctions.isPushout_appTop H)
  have hfsq : IsPullback (inv T.toSpecΓ) (Spec.map f.appTop) f (inv S.toSpecΓ) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, Scheme.toSpecΓ_naturality]⟩
  have hQ' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map g.appTop) :=
    MorphismProperty.of_isPullback hSpec.flip (MorphismProperty.of_isPullback hfsq hQf)
  have hiso : IsPullback T.toSpecΓ f (Spec.map f.appTop) S.toSpecΓ :=
    IsPullback.of_horiz_isIso ⟨(Scheme.toSpecΓ_naturality f).symm⟩
  have hbig : IsPullback (Y.toSpecΓ ≫ Spec.map q.appTop) g (Spec.map f.appTop)
      (X.toSpecΓ ≫ Spec.map p.appTop) := by
    rw [← Scheme.toSpecΓ_naturality, ← Scheme.toSpecΓ_naturality]
    exact H.flip.paste_horiz hiso
  have htop : IsPullback Y.toSpecΓ g (Spec.map g.appTop) X.toSpecΓ :=
    IsPullback.of_right hbig (Scheme.toSpecΓ_naturality g).symm hSpec.flip
  have : MorphismProperty.isomorphisms Scheme.{u} X.toSpecΓ :=
    MorphismProperty.of_isPullback_of_descendsAlong htop hQ'
      (MorphismProperty.isomorphisms.infer_property _)
  exact ⟨this⟩

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency.types false in

/- English proof (translation)
Establish `: IsZariskiLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u})` using `@HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine`. Use `IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ (@Surjective ⊓ @Flat) ?_ ?_` and prove the remaining obligations. Introduce and unpack `X Y f ⟨hl, hs⟩`. Conclude with `⟨hs, IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ f hl⟩`. Introduce `R S Y φ g hφ hfst`.

Take `⟨hs, hfl⟩` from `hφ`. Establish `: Surjective (Spec.map φ)` using `hs`. Establish `: Flat (Spec.map φ)` using `hfl`. Establish `: IsAffineHom (pullback.fst (Spec.map φ) g)` using `hfst`. Establish `: IsAffine (Limits.pullback (Spec.map φ) g)` using `isAffine_of_isAffineHom (pullback.fst (Spec.map φ) g)`.

Establish `: IsAffine Y` using `_root_.GlobalTheory.isAffine_of_isPullback_of_flat_surjective (IsPullback.of_hasPullback (Spec.map φ) g).flip`. Use `show IsAffineHom g`. Use `infer_instance`.
-/
theorem _root_.GlobalTheory.isAffineHom_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@IsAffineHom : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have : IsZariskiLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ (@Surjective ⊓ @Flat) ?_ ?_
  · rintro X Y f ⟨hl, hs⟩
    exact ⟨hs, IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ f hl⟩
  · intro R S Y φ g hφ hfst
    obtain ⟨hs, hfl⟩ := hφ
    have : Surjective (Spec.map φ) := hs
    have : Flat (Spec.map φ) := hfl
    have : IsAffineHom (pullback.fst (Spec.map φ) g) := hfst
    have : IsAffine (Limits.pullback (Spec.map φ) g) :=
      isAffine_of_isAffineHom (pullback.fst (Spec.map φ) g)
    have : IsAffine Y :=
      _root_.GlobalTheory.isAffine_of_isPullback_of_flat_surjective (IsPullback.of_hasPullback (Spec.map φ) g).flip
    show IsAffineHom g
    infer_instance

end Descent

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

/- English proof (translation)
Introduce `S G B T _ _ _ q i hq hi hfl hs hqc hker hT`. Establish `hiq : i ≫ q = 1` using `by rw [hker.w, Hom.one_def]`. Establish `hw : fst G T ≫ q = (fst G T * (snd G T ≫ i)) ≫ q`. Rewrite using `[mul_comp, Category.assoc, hiq, comp_one, _root_.mul_one]`. Establish `hpb : IsPullback (fst G T) (fst G T * (snd G T ≫ i)) q q`.

Use `⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw (fun s => lift s.fst (hker.lift (s.fst⁻¹ * s.snd) (toUnit _) (by` and prove the remaining obligations. Rewrite using `[mul_comp, GrpObj.inv_comp, s.condition, inv_mul_cancel, Hom.one_def])))`. Use the proof step `(fun s => lift_fst _ _) (fun s => ?_) (fun s m h1 h2 => ?_)⟩⟩`. Rewrite using `[comp_mul, lift_fst, ← Category.assoc, lift_snd, hker.lift_fst, mul_inv_cancel_left]`. Use `hom_ext _ _ (by rw [h1, lift_fst]) ?_` and prove the remaining obligations.

Rewrite using `[lift_snd]`. Use `hker.hom_ext ?_ (toUnit_unique _ _)` and prove the remaining obligations. Rewrite using `[hker.lift_fst, ← h1, ← h2, comp_mul, Category.assoc, inv_mul_cancel_left]`. Establish `hfst : IsAffineHom (fst G T).left` using `by show IsAffineHom (pullback.fst G.hom T.hom)`. Conclude with `MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom T.hom).flip hT`.

Conclude with `@MorphismProperty.of_isPullback_of_descendsAlong _ _ _ _ _ _ _ _ _ _ _ _ _root_.GlobalTheory.isAffineHom_descendsAlong_fpqc (hpb.map (Over.forget S)) ⟨⟨hs, hfl⟩, hqc⟩ hfst`.
-/
theorem _root_.GlobalTheory.isAffineHom_of_flatQuotient_of_affine_kernel :
    ∀ (S : Scheme.{0}) (G B T : Over S) [GrpObj G] [GrpObj B] [GrpObj T] (q : G ⟶ B) (i : T ⟶ G),
      IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left →
      IsPullback i (toUnit _) q (η[B]) → IsAffineHom T.hom → IsAffineHom q.left := by
  intro S G B T _ _ _ q i hq hi hfl hs hqc hker hT
  have hiq : i ≫ q = 1 := by rw [hker.w, Hom.one_def]
  have hw : fst G T ≫ q = (fst G T * (snd G T ≫ i)) ≫ q := by
    rw [mul_comp, Category.assoc, hiq, comp_one, _root_.mul_one]
  have hpb : IsPullback (fst G T) (fst G T * (snd G T ≫ i)) q q := by
    refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
      (fun s => lift s.fst (hker.lift (s.fst⁻¹ * s.snd) (toUnit _) (by
        rw [mul_comp, GrpObj.inv_comp, s.condition, inv_mul_cancel, Hom.one_def])))
      (fun s => lift_fst _ _) (fun s => ?_) (fun s m h1 h2 => ?_)⟩⟩
    · rw [comp_mul, lift_fst, ← Category.assoc, lift_snd, hker.lift_fst, mul_inv_cancel_left]
    · refine hom_ext _ _ (by rw [h1, lift_fst]) ?_
      rw [lift_snd]
      refine hker.hom_ext ?_ (toUnit_unique _ _)
      rw [hker.lift_fst, ← h1, ← h2, comp_mul, Category.assoc, inv_mul_cancel_left]
  have hfst : IsAffineHom (fst G T).left := by
    show IsAffineHom (pullback.fst G.hom T.hom)
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom T.hom).flip hT
  exact @MorphismProperty.of_isPullback_of_descendsAlong _ _ _ _ _ _ _ _ _ _ _ _
    _root_.GlobalTheory.isAffineHom_descendsAlong_fpqc (hpb.map (Over.forget S)) ⟨⟨hs, hfl⟩, hqc⟩ hfst

end GlobalTheory
