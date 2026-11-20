import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Use `letI := φ.toAlgebra`. Express the relevant statement in the definitionally equal form `Module.Flat T A`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]`. Introduce and unpack `a ⟨⟨t, ht⟩, hta⟩`. Establish `h1 : φ t * a = 0` using `hta`.

Establish `h2 : ψ (φ t) * ψ a = 0` using `by rw [← map_mul, h1, map_zero]`. Establish `h3 : ψ a = 0` using `(h t (nonZeroDivisors.ne_zero ht)).mul_right_eq_zero.mp h2`. Conclude with `hψ (by rw [h3, map_zero])`.
-/
theorem ringHom_flat_of_injective_of_isUnit {T A B : Type*} [CommRing T] [IsDomain T] [IsBezout T]
    [CommRing A] [CommRing B] (φ : T →+* A) (ψ : A →+* B) (hψ : Function.Injective ψ)
    (h : ∀ t : T, t ≠ 0 → IsUnit (ψ (φ t))) : φ.Flat := by
  letI := φ.toAlgebra
  change Module.Flat T A
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨t, ht⟩, hta⟩
  have h1 : φ t * a = 0 := hta
  have h2 : ψ (φ t) * ψ a = 0 := by rw [← map_mul, h1, map_zero]
  have h3 : ψ a = 0 := (h t (nonZeroDivisors.ne_zero ht)).mul_right_eq_zero.mp h2
  exact hψ (by rw [h3, map_zero])

/- English proof (translation)
Rewrite using `[isSchemeTheoreticallyDominant_iff]`. Establish `: QuasiCompact (f.toImage ≫ f.imageι)` using `by rw [f.toImage_imageι]; infer_instance`. Establish `: QuasiCompact f.toImage` using `QuasiCompact.of_comp f.toImage f.imageι`. Use `Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩) ?_ ?_` and prove the remaining obligations. Use `f.imageι.preimage_iSup (fun U : Y.affineOpens ↦ U.1)` as an intermediate fact.

Rewrite using `[← this, iSup_affineOpens_eq_top]`. Simplify using the standard rewrite rules. Introduce `U`. Rewrite using `[Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, ← RingHom.injective_iff_ker_eq_bot]`. Conclude with `f.toImage_app_injective U`.
-/
theorem isSchemeTheoreticallyDominant_toImage {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  have : QuasiCompact (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  have : QuasiCompact f.toImage := QuasiCompact.of_comp f.toImage f.imageι
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩) ?_ ?_
  · have := f.imageι.preimage_iSup (fun U : Y.affineOpens ↦ U.1)
    rw [← this, iSup_affineOpens_eq_top]
    simp
  · intro U
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      ← RingHom.injective_iff_ker_eq_bot]
    exact f.toImage_app_injective U

/- English proof (translation)
Use `HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun U : G.affineOpens ↦ U) (iSup_affineOpens_eq_top G) fun U ↦ ?_` and prove the remaining obligations. Establish `key : ((Scheme.ΓSpecIso (.of T)).inv ≫ s.appLE ⊤ U le_top) ≫ p.app U = CommRingCat.ofHom (algebraMap T K) ≫ (Scheme.ΓSpecIso (.of K)).inv ≫ z.appLE ⊤ (p ⁻¹ᵁ U) le_top`. Rewrite using `[Scheme.ΓSpecIso_inv_naturality_assoc, Category.assoc, p.app_eq_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Use `congr 1`. Use `(Scheme.Hom.appLE_comp_appLE p s ⊤ U (p ⁻¹ᵁ U) _ _).trans (Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE z (spMap (algebraMap T K)) ⊤ ⊤ (p ⁻¹ᵁ U) _ _).symm)` and prove the remaining obligations.

Use `congr 1`. Establish `hfl : ((Scheme.ΓSpecIso (.of T)).inv ≫ s.appLE ⊤ U le_top).hom.Flat`. Use `ringHom_flat_of_injective_of_isUnit (T := T) _ (p.app U).hom (p.app_injective U) ?_` and prove the remaining obligations. Introduce `t ht`. Establish `h1 : IsUnit (algebraMap T K t)` using `IsUnit.mk0 _ (by simpa using ht)`.

Establish `h2` using `h1.map ((Scheme.ΓSpecIso (.of K)).inv ≫ z.appLE ⊤ (p ⁻¹ᵁ U) le_top).hom`. Establish `h3` using `congrArg (fun φ ↦ CommRingCat.Hom.hom φ t) key`. Conclude with `h3 ▸ h2`. Conclude with `(RingHom.Flat.respectsIso.cancel_left_isIso _ _).mp hfl`.
-/
theorem flat_of_isSchemeTheoreticallyDominant_of_fractionRing (T K : Type) [CommRing T]
    [IsDomain T] [IsBezout T] [Field K] [Algebra T K] [IsFractionRing T K] {Z G : Scheme.{0}}
    (p : Z ⟶ G) [QuasiCompact p] [IsSchemeTheoreticallyDominant p] (s : G ⟶ Sp T) (z : Z ⟶ Sp K)
    (w : p ≫ s = z ≫ spMap (algebraMap T K)) : Flat s := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun U : G.affineOpens ↦ U)
    (iSup_affineOpens_eq_top G) fun U ↦ ?_
  have key : ((Scheme.ΓSpecIso (.of T)).inv ≫ s.appLE ⊤ U le_top) ≫ p.app U =
      CommRingCat.ofHom (algebraMap T K) ≫ (Scheme.ΓSpecIso (.of K)).inv ≫
        z.appLE ⊤ (p ⁻¹ᵁ U) le_top := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, Category.assoc, p.app_eq_appLE,
      Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
    refine (Scheme.Hom.appLE_comp_appLE p s ⊤ U (p ⁻¹ᵁ U) _ _).trans
      (Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE z (spMap (algebraMap T K)) ⊤ ⊤ (p ⁻¹ᵁ U) _ _).symm)
    congr 1
  have hfl : ((Scheme.ΓSpecIso (.of T)).inv ≫ s.appLE ⊤ U le_top).hom.Flat := by
    refine ringHom_flat_of_injective_of_isUnit (T := T) _ (p.app U).hom (p.app_injective U) ?_
    intro t ht
    have h1 : IsUnit (algebraMap T K t) :=
      IsUnit.mk0 _ (by simpa using ht)
    have h2 := h1.map ((Scheme.ΓSpecIso (.of K)).inv ≫ z.appLE ⊤ (p ⁻¹ᵁ U) le_top).hom
    have h3 := congrArg (fun φ ↦ CommRingCat.Hom.hom φ t) key
    exact h3 ▸ h2
  exact (RingHom.Flat.respectsIso.cancel_left_isIso _ _).mp hfl

/- English proof (translation)
Introduce `T K _ _ _ _ _ _ X Z i hi`. Set `j : Sp K ⟶ Sp T` to `spMap (algebraMap T K)`. Establish `hjp : IsPreimmersion j` using `IsPreimmersion.of_isLocalization (nonZeroDivisors T)`. Establish `hjf : Flat j`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`.

Conclude with `RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors T))`. Set `i' : Z.left ⟶ pullback X.hom j` to `i.left`. Establish `hi' : IsClosedImmersion i'` using `hi`. Establish `hw : i' ≫ pullback.snd X.hom j = Z.hom` using `Over.w i`. Set `f : Z.left ⟶ X.left` to `i' ≫ pullback.fst X.hom j`.

Establish `hqc : QuasiCompact f` using `inferInstance`. Establish `: QuasiCompact (f.toImage ≫ f.imageι)` using `by rw [f.toImage_imageι]; infer_instance`. Establish `: QuasiCompact f.toImage` using `QuasiCompact.of_comp f.toImage f.imageι`. Establish `hdom` using `isSchemeTheoreticallyDominant_toImage f`. Establish `hsq : f.toImage ≫ (f.imageι ≫ X.hom) = Z.hom ≫ j`.

Rewrite using `[f.toImage_imageι_assoc, Category.assoc, pullback.condition, reassoc_of% hw]`. Set `Ga : Over (Sp T)` to `Over.mk (f.imageι ≫ X.hom)`. Set `io : Ga ⟶ X` to `Over.homMk f.imageι rfl`. Set `t : Z.left ⟶ pullback (f.imageι ≫ X.hom) j` to `pullback.lift f.toImage Z.hom hsq`. Set `m : pullback (f.imageι ≫ X.hom) j ⟶ pullback X.hom j` to `pullback.map _ _ _ _ f.imageι (𝟙 _) (𝟙 _) (by simp) (by simp)`.

Establish `: MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{0}` using `⟨fun f g hf hg ↦ @IsClosedImmersion.comp _ _ _ f g hf hg⟩`. Establish `hm : IsClosedImmersion m` using `MorphismProperty.pullbackMap (P := @IsClosedImmersion.{0}) inferInstance inferInstance rfl (by simp)`. Establish `htm : t ≫ m = i'`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `[t, m, f, pullback.lift_fst, pullback.lift_fst_assoc]`.

Simplify using `[t, m, hw, pullback.lift_snd]`. Establish `: IsClosedImmersion (t ≫ m)` using `htm ▸ hi'`. Establish `ht : IsClosedImmersion t` using `IsClosedImmersion.of_comp_isClosedImmersion t m`. Establish `hpb : IsPullback (𝟙 Z.left) t f.toImage (pullback.fst (f.imageι ≫ X.hom) j)` using `IsPullback.of_horiz_isIso_mono ⟨by simp [t, pullback.lift_fst]⟩`. Establish `htd : IsSchemeTheoreticallyDominant t` using `.of_isPullback hpb`.

Establish `: IsIso t` using `IsClosedImmersion.isIso_iff_ker_eq_bot.mpr t.ker_eq_bot`. Use `⟨Ga, io, (Over.isoMk (f := Z) (g := (Over.pullback j).obj Ga) (asIso t) ?_).symm, inferInstanceAs (IsClosedImmersion f.imageι), flat_of_isSchemeTheoreticallyDominant_of_fractionRing T K f.toImage _ Z.hom hsq, ?_⟩` and prove the remaining obligations. Conclude with `pullback.lift_snd _ _ _`. Rewrite using `[Iso.symm_hom, Iso.inv_comp_eq]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `i' = t ≫ _`. Rewrite using `[← htm]`. Use `congr 1`.
-/
theorem exists_flat_closure : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (X : Over (Sp T)) (Z : Over (Sp K)) (i : Z ⟶ (Over.pullback (spMap (algebraMap T K))).obj X), IsClosedImmersion i.left → ∃ (Ga : Over (Sp T)) (io : Ga ⟶ X) (e : (Over.pullback (spMap (algebraMap T K))).obj Ga ≅ Z), IsClosedImmersion io.left ∧ Flat Ga.hom ∧ e.hom ≫ i = (Over.pullback (spMap (algebraMap T K))).map io := by
  intro T K _ _ _ _ _ _ X Z i hi
  let j : Sp K ⟶ Sp T := spMap (algebraMap T K)
  have hjp : IsPreimmersion j := IsPreimmersion.of_isLocalization (nonZeroDivisors T)
  have hjf : Flat j := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors T))
  let i' : Z.left ⟶ pullback X.hom j := i.left
  have hi' : IsClosedImmersion i' := hi
  have hw : i' ≫ pullback.snd X.hom j = Z.hom := Over.w i
  let f : Z.left ⟶ X.left := i' ≫ pullback.fst X.hom j
  have hqc : QuasiCompact f := inferInstance
  have : QuasiCompact (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  have : QuasiCompact f.toImage := QuasiCompact.of_comp f.toImage f.imageι
  have hdom := isSchemeTheoreticallyDominant_toImage f
  have hsq : f.toImage ≫ (f.imageι ≫ X.hom) = Z.hom ≫ j := by
    rw [f.toImage_imageι_assoc, Category.assoc, pullback.condition, reassoc_of% hw]
  let Ga : Over (Sp T) := Over.mk (f.imageι ≫ X.hom)
  let io : Ga ⟶ X := Over.homMk f.imageι rfl
  let t : Z.left ⟶ pullback (f.imageι ≫ X.hom) j := pullback.lift f.toImage Z.hom hsq
  let m : pullback (f.imageι ≫ X.hom) j ⟶ pullback X.hom j :=
    pullback.map _ _ _ _ f.imageι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{0} :=
    ⟨fun f g hf hg ↦ @IsClosedImmersion.comp _ _ _ f g hf hg⟩
  have hm : IsClosedImmersion m :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{0}) inferInstance inferInstance rfl (by simp)
  have htm : t ≫ m = i' := by
    apply pullback.hom_ext
    · simp [t, m, f, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp [t, m, hw, pullback.lift_snd]
  have : IsClosedImmersion (t ≫ m) := htm ▸ hi'
  have ht : IsClosedImmersion t := IsClosedImmersion.of_comp_isClosedImmersion t m
  have hpb : IsPullback (𝟙 Z.left) t f.toImage (pullback.fst (f.imageι ≫ X.hom) j) :=
    IsPullback.of_horiz_isIso_mono ⟨by simp [t, pullback.lift_fst]⟩
  have htd : IsSchemeTheoreticallyDominant t := .of_isPullback hpb
  have : IsIso t := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr t.ker_eq_bot
  refine ⟨Ga, io, (Over.isoMk (f := Z) (g := (Over.pullback j).obj Ga) (asIso t) ?_).symm,
    inferInstanceAs (IsClosedImmersion f.imageι),
    flat_of_isSchemeTheoreticallyDominant_of_fractionRing T K f.toImage _ Z.hom hsq, ?_⟩
  · exact pullback.lift_snd _ _ _
  · rw [Iso.symm_hom, Iso.inv_comp_eq]
    apply Over.OverMorphism.ext
    change i' = t ≫ _
    rw [← htm]
    congr 1

end GlobalTheory
