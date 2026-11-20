import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsPrincipalMapAwayOfHasProjectiveDimensionLE
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoPreimageBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasExtOfSetup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemePullbackOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleDivSymm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

/- English proof (translation)
Establish `: IsRegularRing E` using `GlobalTheory.isRegularRing_of_isRegularLocalRing E`. Use `ExtendRig.isRegularRing_stalk isRegularRing_of_smooth E p y` as an intermediate fact. Conclude with `uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing isPrincipal_map_away_of_hasProjectiveDimensionLE _`.
-/
theorem ufm_stalk_of_smooth_regularLocal {E : Type} [CommRing E] [IsRegularLocalRing E] {Y : Scheme.{0}} [IsIntegral Y]
    (p : Y ⟶ Sp E) [Smooth p] (y : Y) : UniqueFactorizationMonoid (Y.presheaf.stalk y) := by
  have : IsRegularRing E := GlobalTheory.isRegularRing_of_isRegularLocalRing E
  have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth E p y
  exact uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing
    isPrincipal_map_away_of_hasProjectiveDimensionLE _

/- English proof (translation)
Introduce `R _ _ _ _ f hf A _ hA L hL hamp hC`. Establish `: IsDomain (Localization.Away f)` using `IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)`. Establish `: IsIntegral A.left` using `isIntegral_left_of_isAbelianScheme A`. Take `⟨D, hD, hsym⟩` from `GlobalTheory.SymDiv.exists_ampleDiv_symm _ A hA L hL hamp`. Set `C : ∀ x : Sp R, Chart (awayMap f) A x` to `fun x => (hC x).some`.

Establish `intC : ∀ x, IsIntegral (C x).G.left` using `fun x =>`. Use `(C x).semi` as an intermediate fact. Use `isIntegral_left_of_isSemiAbelian (C x).G`. Use `choose ρ V φ θ hρ hflat hV hcart hcompat hθ using fun x => chart_part R f hf A hA x (C x)`. Establish `hdiv : ∀ x, ∃ D₁ : CartierDiv (C x).G.left, PPull (V x).ι (φ x) (θ x) D D₁ ∧ ∀ z, Vert (C x).G.hom (ρ x f) z → D₁.IsEqn z 1` using `fun x => by`.

Use `(C x).semi.smooth` as an intermediate fact. Establish `: IsLocallyNoetherian (C x).G.left` using `LocallyOfFiniteType.isLocallyNoetherian (C x).G.hom`. Establish `hρf : Flat (spMap (ρ x))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `hflat x`.

Establish `hφ : Flat (φ x)` using `MorphismProperty.of_isPullback (hcart x).flip hρf`. Take `⟨D₁, h₁, h₂⟩` from `exists_cartierDiv_closure (C x).G.left (V x).toScheme A.left (ufm_stalk_of_smooth_regularLocal (C x).G.hom) (V x).ι (φ x) (θ x) hφ (hθ x) D`. Use `⟨D₁, h₁, fun z hz => h₂ z ?_ hz.1⟩` and prove the remaining obligations. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `fun hzV => (hV x z).1 hzV hz.2`.

Use `choose D₁ hpull hvert using hdiv`. Establish `hamp₁ : ∀ x, AmpleDiv (D₁ x)` using `fun x => by`. Use `(C x).charZero` as an intermediate fact. Establish `hne : ρ x f ≠ 0` using `fun h0 => by`. Take `⟨l, -⟩` from `hθ x`.

Set `v : (V x).toScheme` to `l (closedPoint _)`. Use `(hV x v.1).1 v.2 ?_` and prove the remaining obligations. Rewrite using `[h0]`. Conclude with `zero_mem _`. Conclude with `ampleDiv_closure_on_chart R f A hA D hD hsym (C x).R (C x).complete (ρ x) (hflat x) hne (C x).G (C x).semi (V x) (φ x) (θ x) (D₁ x) (hV x) (hcart x) (C x).y (C x).α (C x).gen (hcompat x) (hθ x) (hpull x)`.

Conclude with `hasExt_of_setup { R := R, f := f, hf := hf, A := A, ab := hA, D := D, amp := hD, C := C, ρ := ρ, hρ := hρ, flat := hflat, V := V, hV := hV, φ := φ, cart := hcart, compat := hcompat, θ := θ, hθ := hθ, D₁ := D₁, pull := hpull, noVert := hvert, amp₁ := hamp₁ }`.
-/
theorem hasExt_awayMap_of_charts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (f : R), f ≠ 0 → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : Sp R, Nonempty (Chart (awayMap f) A x)) → HasExt (awayMap f) A := by
  intro R _ _ _ _ f hf A _ hA L hL hamp hC
  have : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsIntegral A.left := isIntegral_left_of_isAbelianScheme A
  obtain ⟨D, hD, hsym⟩ := GlobalTheory.SymDiv.exists_ampleDiv_symm _ A hA L hL hamp
  let C : ∀ x : Sp R, Chart (awayMap f) A x := fun x => (hC x).some
  have intC : ∀ x, IsIntegral (C x).G.left := fun x =>
    have := (C x).semi
    isIntegral_left_of_isSemiAbelian (C x).G
  choose ρ V φ θ hρ hflat hV hcart hcompat hθ using fun x => chart_part R f hf A hA x (C x)
  have hdiv : ∀ x, ∃ D₁ : CartierDiv (C x).G.left, PPull (V x).ι (φ x) (θ x) D D₁ ∧
      ∀ z, Vert (C x).G.hom (ρ x f) z → D₁.IsEqn z 1 := fun x => by
    have := (C x).semi.smooth
    have : IsLocallyNoetherian (C x).G.left := LocallyOfFiniteType.isLocallyNoetherian (C x).G.hom
    have hρf : Flat (spMap (ρ x)) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact hflat x
    have hφ : Flat (φ x) := MorphismProperty.of_isPullback (hcart x).flip hρf
    obtain ⟨D₁, h₁, h₂⟩ := exists_cartierDiv_closure (C x).G.left (V x).toScheme A.left
      (ufm_stalk_of_smooth_regularLocal (C x).G.hom) (V x).ι (φ x) (θ x) hφ (hθ x) D
    refine ⟨D₁, h₁, fun z hz => h₂ z ?_ hz.1⟩
    rw [Scheme.Opens.range_ι]
    exact fun hzV => (hV x z).1 hzV hz.2
  choose D₁ hpull hvert using hdiv
  have hamp₁ : ∀ x, AmpleDiv (D₁ x) := fun x => by
    have := (C x).charZero
    have hne : ρ x f ≠ 0 := fun h0 => by
      obtain ⟨l, -⟩ := hθ x
      let v : (V x).toScheme := l (closedPoint _)
      refine (hV x v.1).1 v.2 ?_
      rw [h0]
      exact zero_mem _
    exact ampleDiv_closure_on_chart R f A hA D hD hsym (C x).R (C x).complete (ρ x) (hflat x) hne (C x).G (C x).semi (V x) (φ x) (θ x)
      (D₁ x) (hV x) (hcart x) (C x).y (C x).α (C x).gen (hcompat x) (hθ x) (hpull x)
  exact hasExt_of_setup
    { R := R, f := f, hf := hf, A := A, ab := hA, D := D, amp := hD, C := C, ρ := ρ, hρ := hρ, flat := hflat, V := V,
      hV := hV, φ := φ, cart := hcart, compat := hcompat, θ := θ, hθ := hθ, D₁ := D₁, pull := hpull, noVert := hvert,
      amp₁ := hamp₁ }

end GlobalTheory.Desc
