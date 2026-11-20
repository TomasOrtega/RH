import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.CoordinateIdealOrderOne
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.RestrictionToOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealAssignment
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

/- English proof (translation)
The claim follows from `h`.
-/
private theorem le_of_ideal_le {X : Scheme.{u}} {I J : X.IdealSheafData}
    (h : ∀ V : X.affineOpens, I.ideal V ≤ J.ideal V) : I ≤ J := h

/- English proof (translation)
The claim follows from `e.commRingCatIsoToRingEquiv.injective`.
-/
private theorem injective_hom_of_iso {A B : CommRingCat.{u}} (e : A ≅ B) :
    Function.Injective e.hom.hom :=
  e.commRingCatIsoToRingEquiv.injective

/- English proof (translation)
The claim follows from `e.commRingCatIsoToRingEquiv.surjective`.
-/
private theorem surjective_hom_of_iso {A B : CommRingCat.{u}} (e : A ≅ B) :
    Function.Surjective e.hom.hom :=
  e.commRingCatIsoToRingEquiv.surjective

/- English proof (translation)
Introduce `x hx`. Establish `hx0 : e.hom.hom x = e.hom.hom 0`. Simplify `hx` using `[RingHom.mem_ker]`. Establish `hz : x = 0` using `injective_hom_of_iso e hx0`. Simplify using `[hz]`.
-/
private theorem ker_hom_of_iso_le {A B : CommRingCat.{u}} (e : A ≅ B) (I : Ideal A) :
    RingHom.ker e.hom.hom ≤ I := by
  intro x hx
  have hx0 : e.hom.hom x = e.hom.hom 0 := by
    simpa [RingHom.mem_ker] using hx
  have hz : x = 0 := injective_hom_of_iso e hx0
  simp [hz]

/- English proof (translation)
The claim follows from `(Ideal.isRadical_iff_quotient_reduced I).mp (Ideal.radical_eq_iff.mp h)`.
-/
private theorem isReduced_quotient_of_radical_eq {R : Type u} [CommRing R] (I : Ideal R)
    (h : I.radical = I) : _root_.IsReduced (R ⧸ I) :=
  (Ideal.isRadical_iff_quotient_reduced I).mp (Ideal.radical_eq_iff.mp h)

/- English proof (translation)
The claim follows from `@isReduced_localizationPreserves R _ M S _ alg hloc hred`.
-/
private theorem isReduced_of_isLocalization {R S : Type u} [CommRing R] [CommRing S]
    (alg : Algebra R S) (M : Submonoid R) (hloc : @IsLocalization R _ M S _ alg)
    (hred : _root_.IsReduced R) : _root_.IsReduced S :=
  @isReduced_localizationPreserves R _ M S _ alg hloc hred

/- English proof (translation)
The claim follows from `(PrimeSpectrum.isRadical_vanishingIdeal t).radical`.
-/
private theorem radical_primeSpectrum_vanishingIdeal_eq {R : Type u} [CommRing R]
    (t : Set (PrimeSpectrum R)) :
    (PrimeSpectrum.vanishingIdeal t).radical = PrimeSpectrum.vanishingIdeal t :=
  (PrimeSpectrum.isRadical_vanishingIdeal t).radical

/- English proof (translation)
Establish `hst : ∀ y : ↥(J.subscheme), _root_.IsReduced ↑((J.subscheme).presheaf.stalk y)`. Introduce `y`. Take `⟨U, hyU, hU⟩` from `AlgebraicGeometry.Scheme.exists_isAffineOpen_mem (J.subschemeι.base y)`. Establish `hV : IsAffineOpen (J.subschemeι ⁻¹ᵁ U)` using `hU.preimage J.subschemeι`. Establish `hy : y ∈ J.subschemeι ⁻¹ᵁ U` using `hyU`.

Establish `hredq : _root_.IsReduced (↑Γ(X, U) ⧸ J.ideal ⟨U, hU⟩)` using `isReduced_quotient_of_radical_eq _ (hJ ⟨U, hU⟩)`. Establish `hsec : _root_.IsReduced ↑Γ(J.subscheme, J.subschemeι ⁻¹ᵁ U)`. Use `⟨fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `hz`. Apply `injective_hom_of_iso (J.subschemeObjIso ⟨U, hU⟩)` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Use `hredq.eq_zero _ ⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, hn, map_zero]`. Use `show _root_.IsReduced ↑((J.subscheme).presheaf.stalk ((⟨y, hy⟩ : ↥(J.subschemeι ⁻¹ᵁ U)) : ↥(J.subscheme)))`. Conclude with `isReduced_of_isLocalization _ (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (hV.isLocalization_stalk ⟨y, hy⟩) hsec`.

Use `hst` as an intermediate fact. Conclude with `AlgebraicGeometry.isReduced_of_isReduced_stalk _`.
-/
private theorem isReduced_subscheme_of_radical_eq {X : Scheme.{u}} (J : X.IdealSheafData)
    (hJ : ∀ U : X.affineOpens, (J.ideal U).radical = J.ideal U) :
    AlgebraicGeometry.IsReduced J.subscheme := by
  have hst : ∀ y : ↥(J.subscheme), _root_.IsReduced ↑((J.subscheme).presheaf.stalk y) := by
    intro y
    obtain ⟨U, hyU, hU⟩ :=
      AlgebraicGeometry.Scheme.exists_isAffineOpen_mem (J.subschemeι.base y)
    have hV : IsAffineOpen (J.subschemeι ⁻¹ᵁ U) := hU.preimage J.subschemeι
    have hy : y ∈ J.subschemeι ⁻¹ᵁ U := hyU
    have hredq : _root_.IsReduced (↑Γ(X, U) ⧸ J.ideal ⟨U, hU⟩) :=
      isReduced_quotient_of_radical_eq _ (hJ ⟨U, hU⟩)
    have hsec : _root_.IsReduced ↑Γ(J.subscheme, J.subschemeι ⁻¹ᵁ U) := by
      refine ⟨fun z hz => ?_⟩
      obtain ⟨n, hn⟩ := hz
      apply injective_hom_of_iso (J.subschemeObjIso ⟨U, hU⟩)
      rw [map_zero]
      refine hredq.eq_zero _ ⟨n, ?_⟩
      rw [← map_pow, hn, map_zero]
    show _root_.IsReduced
      ↑((J.subscheme).presheaf.stalk ((⟨y, hy⟩ : ↥(J.subschemeι ⁻¹ᵁ U)) : ↥(J.subscheme)))
    exact isReduced_of_isLocalization _ (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
      (hV.isLocalization_stalk ⟨y, hy⟩) hsec
  have := hst
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

/- English proof (translation)
Use `isReduced_subscheme_of_radical_eq _ (fun U => ?_)` and prove the remaining obligations. Rewrite using `[Scheme.IdealSheafData.vanishingIdeal_ideal]`. Conclude with `radical_primeSpectrum_vanishingIdeal_eq _`.
-/
private theorem isReduced_vanishingIdeal_subscheme {X : Scheme.{u}} (Z : Closeds ↥X) :
    AlgebraicGeometry.IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  refine isReduced_subscheme_of_radical_eq _ (fun U => ?_)
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  exact radical_primeSpectrum_vanishingIdeal_eq _

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem support_vanishingIdeal_eq_self {X : Scheme.{u}} (Z : Closeds ↥X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := rfl

/- English proof (translation)
Rewrite using `[← Scheme.IdealSheafData.vanishingIdeal_support]`. Conclude with `Scheme.IdealSheafData.gc.u_l_u_eq_u Z`.
-/
private theorem radical_vanishingIdeal_eq_self {X : Scheme.{u}} (Z : Closeds ↥X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).radical
      = Scheme.IdealSheafData.vanishingIdeal Z := by
  rw [← Scheme.IdealSheafData.vanishingIdeal_support]
  exact Scheme.IdealSheafData.gc.u_l_u_eq_u Z

/- English proof (translation)
Establish `h' : Z ≤ I.support` using `h`. Conclude with `(Scheme.IdealSheafData.gc I Z).mp h'`.
-/
private theorem le_vanishingIdeal_of_subset {X : Scheme.{u}} (I : X.IdealSheafData)
    (Z : Closeds ↥X) (h : (Z : Set ↥X) ⊆ (I.support : Set ↥X)) :
    I ≤ Scheme.IdealSheafData.vanishingIdeal Z := by
  have h' : Z ≤ I.support := h
  exact (Scheme.IdealSheafData.gc I Z).mp h'

/- English proof (translation)
Use `le_antisymm (le_of_ideal_le ?_) (Scheme.IdealSheafData.le_radical _)` and prove the remaining obligations. Introduce `V`. Establish `hV : IsAffineOpen (f ''ᵁ (V : X.Opens))` using `V.2.image_of_isOpenImmersion f`. Establish `e : (V : X.Opens) ≤ f ⁻¹ᵁ (f ''ᵁ (V : X.Opens))` using `fun x hx => ⟨x, hx, rfl⟩`. Establish `hmap` using `Scheme.IdealSheafData.comap_ideal_eq_map_appLE I f ⟨f ''ᵁ (V : X.Opens), hV⟩ V e`.

Establish `hiso : f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e = (f.appIso (V : X.Opens)).hom` using `(Scheme.Hom.appIso_hom' f (V : X.Opens)).symm`. Establish `hsurj : Function.Surjective (f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e).hom`. Rewrite using `[hiso]`. Conclude with `surjective_hom_of_iso _`. Establish `hker : RingHom.ker (f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e).hom ≤ I.ideal ⟨f ''ᵁ (V : X.Opens), hV⟩`.

Rewrite using `[hiso]`. Conclude with `ker_hom_of_iso_le _ _`. Establish `hIrad : (I.ideal ⟨f ''ᵁ (V : X.Opens), hV⟩).radical = I.ideal ⟨f ''ᵁ (V : X.Opens), hV⟩`. Rewrite using `[← Scheme.IdealSheafData.radical_ideal, hI]`. Establish `hrw : ((I.comap f).ideal V).radical = (I.comap f).ideal V`.

Rewrite using `[hmap, ← Ideal.map_radical_of_surjective hsurj hker, hIrad]`. Conclude with `le_of_eq ((Scheme.IdealSheafData.radical_ideal (I.comap f) V).trans hrw)`.
-/
private theorem radical_comap_eq_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsOpenImmersion f] (I : Y.IdealSheafData) (hI : I.radical = I) :
    (I.comap f).radical = I.comap f := by
  refine le_antisymm (le_of_ideal_le ?_) (Scheme.IdealSheafData.le_radical _)
  intro V
  have hV : IsAffineOpen (f ''ᵁ (V : X.Opens)) := V.2.image_of_isOpenImmersion f
  have e : (V : X.Opens) ≤ f ⁻¹ᵁ (f ''ᵁ (V : X.Opens)) := fun x hx => ⟨x, hx, rfl⟩
  have hmap := Scheme.IdealSheafData.comap_ideal_eq_map_appLE I f
    ⟨f ''ᵁ (V : X.Opens), hV⟩ V e
  have hiso : f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e
      = (f.appIso (V : X.Opens)).hom := (Scheme.Hom.appIso_hom' f (V : X.Opens)).symm
  have hsurj : Function.Surjective
      (f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e).hom := by
    rw [hiso]; exact surjective_hom_of_iso _
  have hker : RingHom.ker (f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e).hom
      ≤ I.ideal ⟨f ''ᵁ (V : X.Opens), hV⟩ := by
    rw [hiso]; exact ker_hom_of_iso_le _ _
  have hIrad : (I.ideal ⟨f ''ᵁ (V : X.Opens), hV⟩).radical
      = I.ideal ⟨f ''ᵁ (V : X.Opens), hV⟩ := by
    rw [← Scheme.IdealSheafData.radical_ideal, hI]
  have hrw : ((I.comap f).ideal V).radical = (I.comap f).ideal V := by
    rw [hmap, ← Ideal.map_radical_of_surjective hsurj hker, hIrad]
  exact le_of_eq ((Scheme.IdealSheafData.radical_ideal (I.comap f) V).trans hrw)

/- English proof (translation)
Use `le_antisymm (le_of_ideal_le ?_) (Scheme.IdealSheafData.le_radical _)` and prove the remaining obligations. Introduce `V`. Establish `key : ∀ y : Γ(B, (V : B.Opens)), y ∈ (Scheme.Hom.ker g).ideal V ↔ (Scheme.Hom.app g (V : B.Opens)).hom y = 0`. Introduce `y`. Rewrite using `[← Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ideal_map_of_isAffineHom]`.

Simplify using `[Scheme.IdealSheafData.ideal_bot, Ideal.mem_comap, Pi.bot_apply, Submodule.mem_bot]`. Rewrite using `[Scheme.IdealSheafData.radical_ideal]`. Introduce `y hy`. Take `⟨n, hn⟩` from `hy`. Use `(key y).2 ?_` and prove the remaining obligations.

Establish `: _root_.IsReduced Γ(A, g ⁻¹ᵁ (V : B.Opens))` using `inferInstance`. Use `IsNilpotent.eq_zero ⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow]`. Conclude with `(key _).1 hn`.
-/
private theorem radical_ker_eq_of_isReduced {A B : Scheme.{u}} (g : A ⟶ B)
    [AlgebraicGeometry.IsAffineHom g] [AlgebraicGeometry.IsReduced A] :
    (Scheme.Hom.ker g).radical = Scheme.Hom.ker g := by
  refine le_antisymm (le_of_ideal_le ?_) (Scheme.IdealSheafData.le_radical _)
  intro V
  have key : ∀ y : Γ(B, (V : B.Opens)), y ∈ (Scheme.Hom.ker g).ideal V ↔
      (Scheme.Hom.app g (V : B.Opens)).hom y = 0 := by
    intro y
    rw [← Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ideal_map_of_isAffineHom]
    simp [Scheme.IdealSheafData.ideal_bot, Ideal.mem_comap, Pi.bot_apply, Submodule.mem_bot]
  rw [Scheme.IdealSheafData.radical_ideal]
  intro y hy
  obtain ⟨n, hn⟩ := hy
  refine (key y).2 ?_
  have : _root_.IsReduced Γ(A, g ⁻¹ᵁ (V : B.Opens)) := inferInstance
  refine IsNilpotent.eq_zero ⟨n, ?_⟩
  rw [← map_pow]
  exact (key _).1 hn

/- English proof (translation)
Establish `hker : Scheme.Hom.ker H.subschemeι ≤ Scheme.Hom.ker J.subschemeι`. Rewrite using `[Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]`. Conclude with `h`. Establish `hβfac : AlgebraicGeometry.IsClosedImmersion.lift H.subschemeι J.subschemeι hker ≫ H.subschemeι = J.subschemeι` using `AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ hker`. Establish `hcond : AlgebraicGeometry.IsClosedImmersion.lift H.subschemeι J.subschemeι hker ≫ H.subschemeι = 𝟙 J.subscheme ≫ J.subschemeι`.

Rewrite using `[hβfac, Category.id_comp]`. Use `⟨Limits.pullback.lift _ _ hcond, ?_, Limits.pullback.lift_snd _ _ hcond⟩` and prove the remaining obligations. Apply `Limits.pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Limits.pullback.lift_fst, Category.id_comp]`. Establish `hmono : Mono H.subschemeι` using `inferInstance`.

Apply `hmono.right_cancellation` to reduce the goal to its premises. Rewrite using `[Category.assoc, hβfac, Limits.pullback.condition]`. Rewrite using `[Category.assoc, Limits.pullback.lift_snd, Category.comp_id, Category.id_comp]`.
-/
private theorem isIso_pullback_snd_of_le {X : Scheme.{u}} (H J : X.IdealSheafData)
    (h : H ≤ J) : IsIso (Limits.pullback.snd H.subschemeι J.subschemeι) := by
  have hker : Scheme.Hom.ker H.subschemeι ≤ Scheme.Hom.ker J.subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
    exact h
  have hβfac : AlgebraicGeometry.IsClosedImmersion.lift H.subschemeι J.subschemeι hker
      ≫ H.subschemeι = J.subschemeι :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ hker
  have hcond : AlgebraicGeometry.IsClosedImmersion.lift H.subschemeι J.subschemeι hker
      ≫ H.subschemeι = 𝟙 J.subscheme ≫ J.subschemeι := by
    rw [hβfac, Category.id_comp]
  refine ⟨Limits.pullback.lift _ _ hcond, ?_, Limits.pullback.lift_snd _ _ hcond⟩
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
    have hmono : Mono H.subschemeι := inferInstance
    apply hmono.right_cancellation
    rw [Category.assoc, hβfac, Limits.pullback.condition]
  · rw [Category.assoc, Limits.pullback.lift_snd, Category.comp_id, Category.id_comp]

/- English proof (translation)
Establish `hred : AlgebraicGeometry.IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme` using `isReduced_vanishingIdeal_subscheme Z`. Establish `hHJ : H ≤ Scheme.IdealSheafData.vanishingIdeal Z` using `le_vanishingIdeal_of_subset H Z hZH`. Establish `: IsIso (Limits.pullback.snd H.subschemeι (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)` using `isIso_pullback_snd_of_le H _ hHJ`. Establish `: AlgebraicGeometry.IsOpenImmersion (Limits.pullback.snd H.subschemeι (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)` using `inferInstance`. Establish `: AlgebraicGeometry.IsReduced (Limits.pullback H.subschemeι (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)` using `AlgebraicGeometry.isReduced_of_isOpenImmersion (Limits.pullback.snd H.subschemeι (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)`.

Establish `hrad : ((Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι).radical = (Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι` using `radical_ker_eq_of_isReduced (Limits.pullback.fst H.subschemeι (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)`. Establish `hsupp : ((Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι).support = S`. Apply `SetLike.coe_injective` to reduce the goal to its premises. Rewrite using `[Scheme.IdealSheafData.support_comap]`. Use `show ⇑H.subschemeι ⁻¹' ((Scheme.IdealSheafData.vanishingIdeal Z).support : Set ↥X) = (S : Set ↥(H.subscheme))`.

Rewrite using `[support_vanishingIdeal_eq_self, hS]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem comap_vanishingIdeal_subschemeι {X : Scheme.{u}} (H : X.IdealSheafData)
    (Z : Closeds ↥X) (hZH : (Z : Set ↥X) ⊆ (H.support : Set ↥X))
    (S : Closeds ↥(H.subscheme))
    (hS : (S : Set ↥(H.subscheme)) = H.subschemeι.base ⁻¹' (Z : Set ↥X)) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι =
      Scheme.IdealSheafData.vanishingIdeal S := by
  have hred : AlgebraicGeometry.IsReduced
      (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isReduced_vanishingIdeal_subscheme Z
  have hHJ : H ≤ Scheme.IdealSheafData.vanishingIdeal Z :=
    le_vanishingIdeal_of_subset H Z hZH
  have : IsIso (Limits.pullback.snd H.subschemeι
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) :=
    isIso_pullback_snd_of_le H _ hHJ
  have : AlgebraicGeometry.IsOpenImmersion (Limits.pullback.snd H.subschemeι
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) := inferInstance
  have : AlgebraicGeometry.IsReduced (Limits.pullback H.subschemeι
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) :=
    AlgebraicGeometry.isReduced_of_isOpenImmersion (Limits.pullback.snd H.subschemeι
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)
  have hrad : ((Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι).radical
      = (Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι :=
    radical_ker_eq_of_isReduced (Limits.pullback.fst H.subschemeι
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι).support = S := by
    apply SetLike.coe_injective
    rw [Scheme.IdealSheafData.support_comap]
    show ⇑H.subschemeι ⁻¹'
      ((Scheme.IdealSheafData.vanishingIdeal Z).support : Set ↥X) = (S : Set ↥(H.subscheme))
    rw [support_vanishingIdeal_eq_self, hS]
  calc (Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι
      = ((Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι).radical := hrad.symm
    _ = Scheme.IdealSheafData.vanishingIdeal
          (((Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι).support) :=
        Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = Scheme.IdealSheafData.vanishingIdeal S := by rw [hsupp]

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.support_comap]`. Use `show ⇑U.ι ⁻¹' ((Scheme.IdealSheafData.vanishingIdeal T).support : Set ↥W) = ⇑U.ι ⁻¹' (T : Set ↥W)`. Rewrite using `[support_vanishingIdeal_eq_self]`.
-/
private theorem support_comap_opens_vanishingIdeal {W : Scheme.{u}} (U : W.Opens) (T : Closeds ↥W) :
    ((((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι).support) : Set ↥(U.toScheme))
      = U.ι.base ⁻¹' (T : Set ↥W) := by
  rw [Scheme.IdealSheafData.support_comap]
  show ⇑U.ι ⁻¹' ((Scheme.IdealSheafData.vanishingIdeal T).support : Set ↥W)
    = ⇑U.ι ⁻¹' (T : Set ↥W)
  rw [support_vanishingIdeal_eq_self]

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.vanishingIdeal_support]`. Conclude with `(radical_comap_eq_of_isOpenImmersion U.ι _ (radical_vanishingIdeal_eq_self T)).symm`.
-/
private theorem comap_opens_vanishingIdeal_eq_vanishingIdeal_support {W : Scheme.{u}} (U : W.Opens)
    (T : Closeds ↥W) :
    (Scheme.IdealSheafData.vanishingIdeal T).comap U.ι
      = Scheme.IdealSheafData.vanishingIdeal
          (((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι).support) := by
  rw [Scheme.IdealSheafData.vanishingIdeal_support]
  exact (radical_comap_eq_of_isOpenImmersion U.ι _ (radical_vanishingIdeal_eq_self T)).symm

/- English proof (translation)
Rewrite using `[comap_opens_vanishingIdeal_eq_vanishingIdeal_support U T]`. Use `le_vanishingIdeal_of_subset H _ ?_` and prove the remaining obligations. Rewrite using `[support_comap_opens_vanishingIdeal]`. Conclude with `hTsubH`.
-/
private theorem le_comap_vanishingIdeal_of_preimage_subset {W : Scheme.{u}} (U : W.Opens)
    (H : (U.toScheme).IdealSheafData) (T : Closeds ↥W)
    (hTsubH : (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme))) :
    H ≤ (Scheme.IdealSheafData.vanishingIdeal T).comap U.ι := by
  rw [comap_opens_vanishingIdeal_eq_vanishingIdeal_support U T]
  refine le_vanishingIdeal_of_subset H _ ?_
  rw [support_comap_opens_vanishingIdeal]
  exact hTsubH

/- English proof (translation)
Rewrite using `[comap_opens_vanishingIdeal_eq_vanishingIdeal_support U T]`. Use `comap_vanishingIdeal_subschemeι H _ ?_ S ?_` and prove the remaining obligations. Rewrite using `[support_comap_opens_vanishingIdeal]`. Conclude with `hTsubH`. Rewrite using `[hS, support_comap_opens_vanishingIdeal, ← Set.preimage_comp]`.

Both sides reduce to the same expression.
-/
private theorem comap_subschemeι_comap_vanishingIdeal {W : Scheme.{u}} (U : W.Opens)
    (H : (U.toScheme).IdealSheafData)
    (T : Closeds ↥W) (S : Closeds ↥(H.subscheme))
    (hS : (S : Set ↥(H.subscheme)) = (H.subschemeι ≫ U.ι).base ⁻¹' (T : Set ↥W))
    (hTsubH : (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme))) :
    ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι).comap H.subschemeι =
      Scheme.IdealSheafData.vanishingIdeal S := by
  rw [comap_opens_vanishingIdeal_eq_vanishingIdeal_support U T]
  refine comap_vanishingIdeal_subschemeι H _ ?_ S ?_
  · rw [support_comap_opens_vanishingIdeal]
    exact hTsubH
  · rw [hS, support_comap_opens_vanishingIdeal, ← Set.preimage_comp]
    rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨(I.comapIso f).hom, inferInstance, Scheme.IdealSheafData.comapIso_hom_fst I f⟩`.
-/
private theorem exists_isIso_pullback_lift_comap_subschemeι {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    ∃ α : (I.comap f).subscheme ⟶ Limits.pullback f I.subschemeι,
      IsIso α ∧ α ≫ Limits.pullback.fst f I.subschemeι = (I.comap f).subschemeι :=
  ⟨(I.comapIso f).hom, inferInstance, Scheme.IdealSheafData.comapIso_hom_fst I f⟩

/- English proof (translation)
Take `⟨α, hα, hαfac⟩` from `exists_isIso_pullback_lift_comap_subschemeι f I`. Establish `key : (I.comap f).subschemeι ≫ f ≫ g = α ≫ (Limits.pullback.snd f I.subschemeι ≫ I.subschemeι ≫ g)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Limits.pullback.condition]`. Use `_ = α ≫ (Limits.pullback.snd f I.subschemeι ≫ I.subschemeι ≫ g) := by simp`.

Rewrite using `[key]`. Use `hα` as an intermediate fact. Use `hsm` as an intermediate fact. Use `hsnd` as an intermediate fact. Use `infer_instance`.
-/
private theorem smooth_comap_subschemeι_comp_of_smooth_pullback_snd {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (g : Y ⟶ S)
    (hsm : AlgebraicGeometry.Smooth (I.subschemeι ≫ g))
    (hsnd : AlgebraicGeometry.Smooth (Limits.pullback.snd f I.subschemeι)) :
    AlgebraicGeometry.Smooth ((I.comap f).subschemeι ≫ f ≫ g) := by
  obtain ⟨α, hα, hαfac⟩ := exists_isIso_pullback_lift_comap_subschemeι f I
  have key : (I.comap f).subschemeι ≫ f ≫ g
      = α ≫ (Limits.pullback.snd f I.subschemeι ≫ I.subschemeι ≫ g) := by
    calc (I.comap f).subschemeι ≫ f ≫ g
        = (α ≫ Limits.pullback.fst f I.subschemeι) ≫ f ≫ g := by rw [hαfac]
      _ = α ≫ ((Limits.pullback.fst f I.subschemeι ≫ f) ≫ g) := by simp
      _ = α ≫ ((Limits.pullback.snd f I.subschemeι ≫ I.subschemeι) ≫ g) := by
            rw [Limits.pullback.condition]
      _ = α ≫ (Limits.pullback.snd f I.subschemeι ≫ I.subschemeι ≫ g) := by simp
  rw [key]
  have := hα
  have := hsm
  have := hsnd
  infer_instance

/- English proof (translation)
Assemble the required witnesses or components as `⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x, mem_irreducibleComponent⟩`.
-/
private theorem exists_irreducibleComponent_mem (α : Type u) [TopologicalSpace α] (x : α) :
    ∃ C ∈ irreducibleComponents α, x ∈ C :=
  ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x,
    mem_irreducibleComponent⟩

/- English proof (translation)
Establish `hrad` using `radical_comap_eq_of_isOpenImmersion f (Scheme.IdealSheafData.vanishingIdeal T) (radical_vanishingIdeal_eq_self T)`. Establish `hsupp : ((Scheme.IdealSheafData.vanishingIdeal T).comap f).support = S`. Apply `SetLike.coe_injective` to reduce the goal to its premises. Rewrite using `[Scheme.IdealSheafData.support_comap]`. Use `show ⇑f ⁻¹' ((Scheme.IdealSheafData.vanishingIdeal T).support : Set ↥Y) = (S : Set ↥X)`.

Rewrite using `[support_vanishingIdeal_eq_self, hS]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem comap_vanishingIdeal_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsOpenImmersion f] (T : Closeds ↥Y) (S : Closeds ↥X)
    (hS : (S : Set ↥X) = f.base ⁻¹' (T : Set ↥Y)) :
    (Scheme.IdealSheafData.vanishingIdeal T).comap f =
      Scheme.IdealSheafData.vanishingIdeal S := by
  have hrad := radical_comap_eq_of_isOpenImmersion f
    (Scheme.IdealSheafData.vanishingIdeal T) (radical_vanishingIdeal_eq_self T)
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal T).comap f).support = S := by
    apply SetLike.coe_injective
    rw [Scheme.IdealSheafData.support_comap]
    show ⇑f ⁻¹' ((Scheme.IdealSheafData.vanishingIdeal T).support : Set ↥Y) = (S : Set ↥X)
    rw [support_vanishingIdeal_eq_self, hS]
  calc (Scheme.IdealSheafData.vanishingIdeal T).comap f
      = ((Scheme.IdealSheafData.vanishingIdeal T).comap f).radical := hrad.symm
    _ = Scheme.IdealSheafData.vanishingIdeal
          (((Scheme.IdealSheafData.vanishingIdeal T).comap f).support) :=
        Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = Scheme.IdealSheafData.vanishingIdeal S := by rw [hsupp]

/- English proof (translation)
Introduce `W N U H T S x hS hTsubH hN`. Simplify using `only [vanishingIdealAssignment_apply] at hN ⊢`. Take `⟨V, hxV, hVeq⟩` from `(agreeNear_iff _ _ _).1 hN`. Establish `hrange : Set.range ⇑(((H.subschemeι ≫ U.ι) ⁻¹ᵁ V).ι ≫ H.subschemeι ≫ U.ι) ⊆ Set.range ⇑V.ι`. Rewrite using `[Scheme.Opens.range_ι]`.

Introduce and unpack `z ⟨y, rfl⟩`. Establish `hy : ((H.subschemeι ≫ U.ι) ⁻¹ᵁ V).ι y ∈ (((H.subschemeι ≫ U.ι) ⁻¹ᵁ V : (H.subscheme).Opens) : Set ↥(H.subscheme))`. Rewrite using `[← Scheme.Opens.range_ι ((H.subschemeι ≫ U.ι) ⁻¹ᵁ V)]`. Conclude with `⟨y, rfl⟩`. Conclude with `hy`.

Take `⟨g, hg⟩ : ∃ g : ((H.subschemeι ≫ U.ι) ⁻¹ᵁ V).toScheme ⟶ V.toScheme, g ≫ V.ι = ((H.subschemeι ≫ U.ι) ⁻¹ᵁ V).ι ≫ H.subschemeι ≫ U.ι` from `⟨AlgebraicGeometry.IsOpenImmersion.lift V.ι _ hrange, AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrange⟩`. Use `(agreeNear_iff _ _ _).2 ⟨(H.subschemeι ≫ U.ι) ⁻¹ᵁ V, hxV, ?_⟩` and prove the remaining obligations. Establish `e : ∀ I : W.IdealSheafData, ((I.comap U.ι).comap H.subschemeι).comap ((H.subschemeι ≫ U.ι) ⁻¹ᵁ V).ι = (I.comap V.ι).comap g`. Introduce `I`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Category.assoc, ← hg, ← Scheme.IdealSheafData.comap_comp]`.

Rewrite using `[e N, hVeq, ← e, comap_subschemeι_comap_vanishingIdeal U H T S hS hTsubH]`.
-/
theorem agreeNearVanishingComapSubscheme : AgreeNearVanishingComapSubscheme.{u} := by
  intro W N U H T S x hS hTsubH hN
  simp only [vanishingIdealAssignment_apply] at hN ⊢
  obtain ⟨V, hxV, hVeq⟩ := (agreeNear_iff _ _ _).1 hN
  have hrange : Set.range ⇑(((H.subschemeι ≫ U.ι) ⁻¹ᵁ V).ι ≫ H.subschemeι ≫ U.ι)
      ⊆ Set.range ⇑V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro z ⟨y, rfl⟩
    have hy : ((H.subschemeι ≫ U.ι) ⁻¹ᵁ V).ι y
        ∈ (((H.subschemeι ≫ U.ι) ⁻¹ᵁ V : (H.subscheme).Opens) : Set ↥(H.subscheme)) := by
      rw [← Scheme.Opens.range_ι ((H.subschemeι ≫ U.ι) ⁻¹ᵁ V)]
      exact ⟨y, rfl⟩
    exact hy
  obtain ⟨g, hg⟩ : ∃ g : ((H.subschemeι ≫ U.ι) ⁻¹ᵁ V).toScheme ⟶ V.toScheme,
      g ≫ V.ι = ((H.subschemeι ≫ U.ι) ⁻¹ᵁ V).ι ≫ H.subschemeι ≫ U.ι :=
    ⟨AlgebraicGeometry.IsOpenImmersion.lift V.ι _ hrange,
      AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrange⟩
  refine (agreeNear_iff _ _ _).2 ⟨(H.subschemeι ≫ U.ι) ⁻¹ᵁ V, hxV, ?_⟩
  have e : ∀ I : W.IdealSheafData,
      ((I.comap U.ι).comap H.subschemeι).comap ((H.subschemeι ≫ U.ι) ⁻¹ᵁ V).ι
        = (I.comap V.ι).comap g := by
    intro I
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Category.assoc,
      ← hg, ← Scheme.IdealSheafData.comap_comp]
  rw [e N, hVeq, ← e, comap_subschemeι_comap_vanishingIdeal U H T S hS hTsubH]

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hsm`.
-/
theorem smooth_subschemeι_comp_of_eq {X S : Scheme.{u}} (f : X ⟶ S) {K K' : X.IdealSheafData}
    (h : K = K') (hsm : AlgebraicGeometry.Smooth (K'.subschemeι ≫ f)) :
    AlgebraicGeometry.Smooth (K.subschemeι ≫ f) := by
  subst h
  exact hsm

/- English proof (translation)
Establish `: AlgebraicGeometry.Smooth (Limits.pullback.snd f I.subschemeι)` using `inferInstance`. Conclude with `smooth_comap_subschemeι_comp_of_smooth_pullback_snd f I g hsm inferInstance`.
-/
theorem smooth_comap_subschemeι_of_isOpenImmersion {X Y S : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsOpenImmersion f] (I : Y.IdealSheafData) (g : Y ⟶ S)
    (hsm : AlgebraicGeometry.Smooth (I.subschemeι ≫ g)) :
    AlgebraicGeometry.Smooth ((I.comap f).subschemeι ≫ f ≫ g) := by
  have : AlgebraicGeometry.Smooth (Limits.pullback.snd f I.subschemeι) := inferInstance
  exact smooth_comap_subschemeι_comp_of_smooth_pullback_snd f I g hsm inferInstance

/- English proof (translation)
Establish `hcomap` using `comap_subschemeι_comap_vanishingIdeal U H T S hS hTsubH`. Use `smooth_subschemeι_comp_of_eq (H.subschemeι ≫ U.ι ≫ p) hcomap.symm ?_` and prove the remaining obligations. Establish `hJ : AlgebraicGeometry.Smooth (((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι).subschemeι ≫ U.ι ≫ p)` using `smooth_comap_subschemeι_of_isOpenImmersion U.ι (Scheme.IdealSheafData.vanishingIdeal T) p hT`. Establish `: IsIso (Limits.pullback.snd H.subschemeι ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι).subschemeι)` using `isIso_pullback_snd_of_le H _ (le_comap_vanishingIdeal_of_preimage_subset U H T hTsubH)`. Establish `hsnd : AlgebraicGeometry.Smooth (Limits.pullback.snd H.subschemeι ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι).subschemeι)` using `inferInstance`.

Conclude with `smooth_comap_subschemeι_comp_of_smooth_pullback_snd H.subschemeι ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι) (U.ι ≫ p) hJ hsnd`.
-/
theorem smooth_vanishingIdeal_comap_subschemeι {k : Type u} [Field k] {W : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) (H : (U.toScheme).IdealSheafData)
    (_hH : FunctorialResolution.EmbeddedResolution.IsSmoothDivisor (U.ι ≫ p) H)
    (T : Closeds ↥W) (S : Closeds ↥(H.subscheme))
    (hS : (S : Set ↥(H.subscheme)) = (H.subschemeι ≫ U.ι).base ⁻¹' (T : Set ↥W))
    (hTsubH : (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme)))
    (hT : AlgebraicGeometry.Smooth ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p)) :
    AlgebraicGeometry.Smooth
      ((Scheme.IdealSheafData.vanishingIdeal S).subschemeι ≫ H.subschemeι ≫ U.ι ≫ p) := by
  have hcomap := comap_subschemeι_comap_vanishingIdeal U H T S hS hTsubH
  refine smooth_subschemeι_comp_of_eq (H.subschemeι ≫ U.ι ≫ p) hcomap.symm ?_
  have hJ : AlgebraicGeometry.Smooth
      (((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι).subschemeι ≫ U.ι ≫ p) :=
    smooth_comap_subschemeι_of_isOpenImmersion U.ι
      (Scheme.IdealSheafData.vanishingIdeal T) p hT
  have : IsIso (Limits.pullback.snd H.subschemeι
      ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι).subschemeι) :=
    isIso_pullback_snd_of_le H _ (le_comap_vanishingIdeal_of_preimage_subset U H T hTsubH)
  have hsnd : AlgebraicGeometry.Smooth (Limits.pullback.snd H.subschemeι
      ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι).subschemeι) := inferInstance
  exact smooth_comap_subschemeι_comp_of_smooth_pullback_snd H.subschemeι
    ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι) (U.ι ≫ p) hJ hsnd

/- English proof (translation)
Establish `hp' : AlgebraicGeometry.Smooth p` using `hp`. Establish `hsm' : AlgebraicGeometry.Smooth ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p)` using `hsm`. Establish `hZs : (Scheme.IdealSheafData.vanishingIdeal T).support = T` using `support_vanishingIdeal_eq_self T`. Establish `hxZ : x ∈ (Scheme.IdealSheafData.vanishingIdeal T).support`. Rewrite using `[hZs]`.

Conclude with `hx`. Take `⟨U, m, c, S, hxU, hU, hD⟩` from `FunctorialResolution.EmbeddedResolution.exists_chart_restrictIdeal_eq_coordIdeal p (Scheme.IdealSheafData.vanishingIdeal T) x hxZ`. Break down `S.eq_empty_or_nonempty with hSe | ⟨j, hj⟩` into its components or cases. It suffices to derive a contradiction. Establish `key : ∀ y : ↥(U.toScheme), FunctorialResolution.EmbeddedResolution.orderAt (Scheme.IdealSheafData.vanishingIdeal T) (U.ι.base y) = ⊤`.

Introduce `y`. Establish `h1 : FunctorialResolution.EmbeddedResolution.restrictIdeal (Scheme.IdealSheafData.vanishingIdeal T) U = c.coordIdeal (∅ : Finset (Fin m))` using `by rw [hD, hSe]`. Establish `h2 : (Scheme.IdealSheafData.vanishingIdeal T).comap U.ι = (⊥ : (FunctorialResolution.EmbeddedResolution.affineSpaceFin k m).IdealSheafData).comap c.map`. Rewrite using `[← FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_comap_ι, h1, FunctorialResolution.EmbeddedResolution.EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, FunctorialResolution.EmbeddedResolution.coordSubspaceIdeal_empty]`. Establish `h3 : FunctorialResolution.EmbeddedResolution.stalkIdeal ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι) y = FunctorialResolution.EmbeddedResolution.stalkIdeal (⊥ : (U.toScheme).IdealSheafData) y`.

Rewrite using `[h2, FunctorialResolution.EmbeddedResolution.stalkIdeal_comap, FunctorialResolution.EmbeddedResolution.stalkIdeal_bot, Ideal.map_bot, FunctorialResolution.EmbeddedResolution.stalkIdeal_bot]`. Establish `h4 : FunctorialResolution.EmbeddedResolution.orderAt ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι) y = ⊤`. Rewrite using `[FunctorialResolution.EmbeddedResolution.orderAt_eq_of_stalkIdeal_eq h3, FunctorialResolution.EmbeddedResolution.orderAt_bot]`. Conclude with `(FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion U.ι (Scheme.IdealSheafData.vanishingIdeal T) y).symm.trans h4`. Establish `hUsubT : (U : Set ↥W) ⊆ (T : Set ↥W)`.

Introduce `z hz`. Establish `hrange : Set.range U.ι.base = (U : Set ↥W)` using `by simp`. Take `⟨y, rfl⟩ : z ∈ Set.range U.ι.base` from `by rw [hrange]; exact hz`. Establish `h6 : (1 : ℕ∞) ≤ FunctorialResolution.EmbeddedResolution.orderAt (Scheme.IdealSheafData.vanishingIdeal T) (U.ι.base y)`. Rewrite using `[key y]`.

Conclude with `le_top`. Establish `h7` using `(FunctorialResolution.EmbeddedResolution.one_le_orderAt_iff_mem_support _ _).1 h6`. Rewrite `h7` using `[hZs]`. Conclude with `h7`. Take `⟨C, hC, hxC⟩` from `exists_irreducibleComponent_mem (↥W) x`.

Use `hcomp C hC ?_` and prove the remaining obligations. Introduce `z hzC`. Assume the negation of the conclusion as `hzT`. Take `⟨w, hwC, hwU, hwT⟩` from `hC.1.2 (U : Set ↥W) ((T : Set ↥W)ᶜ) U.isOpen T.2.isOpen_compl ⟨x, hxC, hxU⟩ ⟨z, hzC, hzT⟩`. Conclude with `hwT (hUsubT hwU)`.

Conclude with `FunctorialResolution.EmbeddedResolution.orderAt_eq_one_of_restrictIdeal_eq_coordIdeal p hU c S j hj (Scheme.IdealSheafData.vanishingIdeal T) hD x hxU hxZ`.
-/
theorem orderAt_vanishingIdeal_eq_one {k : Type u} [Field k] [CharZero k] {W : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (hp : AlgebraicGeometry.Smooth p) (T : Closeds ↥W)
    (_hirr : IsIrreducible (T : Set ↥W))
    (hsm : AlgebraicGeometry.Smooth ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p))
    (hcomp : ∀ C ∈ irreducibleComponents ↥W, ¬ C ⊆ (T : Set ↥W))
    (x : ↥W) (hx : x ∈ (T : Set ↥W)) :
    FunctorialResolution.EmbeddedResolution.orderAt (Scheme.IdealSheafData.vanishingIdeal T) x = 1 := by
  have hp' : AlgebraicGeometry.Smooth p := hp
  have hsm' : AlgebraicGeometry.Smooth
      ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p) := hsm
  have hZs : (Scheme.IdealSheafData.vanishingIdeal T).support = T :=
    support_vanishingIdeal_eq_self T
  have hxZ : x ∈ (Scheme.IdealSheafData.vanishingIdeal T).support := by
    rw [hZs]; exact hx
  obtain ⟨U, m, c, S, hxU, hU, hD⟩ :=
    FunctorialResolution.EmbeddedResolution.exists_chart_restrictIdeal_eq_coordIdeal p
      (Scheme.IdealSheafData.vanishingIdeal T) x hxZ
  rcases S.eq_empty_or_nonempty with hSe | ⟨j, hj⟩
  · exfalso
    have key : ∀ y : ↥(U.toScheme),
        FunctorialResolution.EmbeddedResolution.orderAt (Scheme.IdealSheafData.vanishingIdeal T) (U.ι.base y) = ⊤ := by
      intro y
      have h1 : FunctorialResolution.EmbeddedResolution.restrictIdeal (Scheme.IdealSheafData.vanishingIdeal T) U
          = c.coordIdeal (∅ : Finset (Fin m)) := by rw [hD, hSe]
      have h2 : (Scheme.IdealSheafData.vanishingIdeal T).comap U.ι
          = (⊥ : (FunctorialResolution.EmbeddedResolution.affineSpaceFin k m).IdealSheafData).comap c.map := by
        rw [← FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_comap_ι, h1, FunctorialResolution.EmbeddedResolution.EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal,
          FunctorialResolution.EmbeddedResolution.coordSubspaceIdeal_empty]
      have h3 : FunctorialResolution.EmbeddedResolution.stalkIdeal ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι) y
          = FunctorialResolution.EmbeddedResolution.stalkIdeal (⊥ : (U.toScheme).IdealSheafData) y := by
        rw [h2, FunctorialResolution.EmbeddedResolution.stalkIdeal_comap, FunctorialResolution.EmbeddedResolution.stalkIdeal_bot, Ideal.map_bot,
          FunctorialResolution.EmbeddedResolution.stalkIdeal_bot]
      have h4 : FunctorialResolution.EmbeddedResolution.orderAt ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι) y = ⊤ := by
        rw [FunctorialResolution.EmbeddedResolution.orderAt_eq_of_stalkIdeal_eq h3, FunctorialResolution.EmbeddedResolution.orderAt_bot]
      exact (FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion U.ι
        (Scheme.IdealSheafData.vanishingIdeal T) y).symm.trans h4
    have hUsubT : (U : Set ↥W) ⊆ (T : Set ↥W) := by
      intro z hz
      have hrange : Set.range U.ι.base = (U : Set ↥W) := by simp
      obtain ⟨y, rfl⟩ : z ∈ Set.range U.ι.base := by rw [hrange]; exact hz
      have h6 : (1 : ℕ∞) ≤ FunctorialResolution.EmbeddedResolution.orderAt (Scheme.IdealSheafData.vanishingIdeal T)
          (U.ι.base y) := by
        rw [key y]; exact le_top
      have h7 := (FunctorialResolution.EmbeddedResolution.one_le_orderAt_iff_mem_support _ _).1 h6
      rw [hZs] at h7
      exact h7
    obtain ⟨C, hC, hxC⟩ := exists_irreducibleComponent_mem (↥W) x
    refine hcomp C hC ?_
    intro z hzC
    by_contra hzT
    obtain ⟨w, hwC, hwU, hwT⟩ := hC.1.2 (U : Set ↥W) ((T : Set ↥W)ᶜ) U.isOpen
      T.2.isOpen_compl ⟨x, hxC, hxU⟩ ⟨z, hzC, hzT⟩
    exact hwT (hUsubT hwU)
  · exact FunctorialResolution.EmbeddedResolution.orderAt_eq_one_of_restrictIdeal_eq_coordIdeal p hU c S j hj
      (Scheme.IdealSheafData.vanishingIdeal T) hD x hxU hxZ

end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

end
