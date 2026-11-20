import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExtendRig

/- English proof (translation)
Establish `: IsNoetherianRing R` using `IsLocalization.isNoetherianRing M R inferInstance`. Rewrite using `[isRegularRing_iff]`. Introduce `q hq`. Establish `h : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap B R))` using `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime q) q`. Conclude with `IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (q.comap (algebraMap B R)).primeCompl (Localization.AtPrime (q.comap (algebraMap B R))) (Localization.AtPrime q)).toRingEquiv`.
-/
theorem isRegularRing_of_isLocalization {B : Type} [CommRing B] [IsRegularRing B]
    (M : Submonoid B) (R : Type) [CommRing R] [Algebra B R] [IsLocalization M R] :
    IsRegularRing R := by
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing M R inferInstance
  rw [isRegularRing_iff]
  intro q hq
  have h : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap B R)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (q.comap (algebraMap B R)).primeCompl
      (Localization.AtPrime (q.comap (algebraMap B R))) (Localization.AtPrime q)).toRingEquiv

/- English proof (translation)
The claim follows from `have : IsDedekindDomain V := IsPrincipalIdealRing.isDedekindDomain V inferInstance`.
-/
theorem isRegularRing_of_isDiscreteValuationRing (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] : IsRegularRing V :=
  have : IsDedekindDomain V := IsPrincipalIdealRing.isDedekindDomain V
  inferInstance

/- English proof (translation)
Use `(IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers π) (S := K) (nonZeroDivisors V) (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) ?_).mpr inferInstance` and prove the remaining obligations. Introduce `a ha`. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero ha) hπ`. Conclude with `⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩`.
-/
theorem isLocalization_away_of_irreducible (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    {π : V} (hπ : Irreducible π) : IsLocalization.Away π K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers π) (S := K)
    (nonZeroDivisors V) (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) ?_).mpr
    inferInstance
  intro a ha
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero ha) hπ
  exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩

/- English proof (translation)
Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Use `isLocalization_away_of_irreducible V K hπ` as an intermediate fact. Conclude with `IsOpenImmersion.of_isLocalization π`.
-/
theorem isOpenImmersion_etaK (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] :
    IsOpenImmersion (etaK V K) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := isLocalization_away_of_irreducible V K hπ
  exact IsOpenImmersion.of_isLocalization π

/- English proof (translation)
Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Establish `hs : (f.appLE ⊤ U le_top).hom.Smooth` using `HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top`. Establish `: IsRegularRing Γ(Spec (CommRingCat.of V), ⊤)` using `IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.symm`. Use `algebraize [(f.appLE ⊤ U le_top).hom]`. Establish `: IsRegularRing Γ(X, U)` using `hreg Γ(Spec (CommRingCat.of V), ⊤) Γ(X, U)`.

Set `` to `X.presheaf.algebra_section_stalk ⟨x, hxU⟩`. Use `hU.isLocalization_stalk ⟨x, hxU⟩` as an intermediate fact. Conclude with `isRegularRing_of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _`.
-/
theorem isRegularRing_stalk
    (hreg : ∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B]
      [Algebra.Smooth V B], IsRegularRing B)
    (V : Type) [CommRing V] [IsRegularRing V] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V))
    [Smooth f] (x : X) : IsRegularRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hs : (f.appLE ⊤ U le_top).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have : IsRegularRing Γ(Spec (CommRingCat.of V), ⊤) :=
    IsRegularRing.of_ringEquiv
      (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.symm
  algebraize [(f.appLE ⊤ U le_top).hom]
  have : IsRegularRing Γ(X, U) := hreg Γ(Spec (CommRingCat.of V), ⊤) Γ(X, U)
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact isRegularRing_of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _

/- English proof (translation)
Introduce `hint hreg hufd hext V _ _ _ K _ _ _ G _ _ _ _ _ _ eA _ L hL _ _`. Establish `hV : IsRegularRing V` using `isRegularRing_of_isDiscreteValuationRing V`. Establish `: GeometricallyIntegral G.hom` using `hint _ _ _ inferInstance inferInstance`. Establish `: IsIntegral G.left` using `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom`. Establish `: IsLocallyNoetherian G.left` using `LocallyOfFiniteType.isLocallyNoetherian G.hom`.

Establish `: CompactSpace G.left` using `QuasiCompact.compactSpace_of_compactSpace G.hom`. Use `isOpenImmersion_etaK V K` as an intermediate fact. Establish `hj : IsOpenImmersion (jA V K G)` using `inferInstance`. Establish `hst : ∀ x : G.left, UniqueFactorizationMonoid (G.left.presheaf.stalk x)` using `fun x =>`. Use `isRegularRing_stalk hreg V G.hom x` as an intermediate fact.

Use `hufd _`. Take `⟨L', hL', φ, hφ⟩` from `hext G.left _ (jA V K G) hj hst L hL`. Take `⟨e, he⟩` from `DVR.exists_gen_of_local (V := V) L' hL' (K := PUnit) (fun _ => eSec G) (fun _ => 1)`. Conclude with `⟨⟨L', e, hL', he⟩, φ, hφ⟩`.
-/
theorem extend_exists :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B] [Algebra.Smooth V B], IsRegularRing B) → (∀ (R : Type) [CommRing R] [IsRegularRing R] [IsLocalRing R] [IsDomain R], UniqueFactorizationMonoid R) → (∀ (X Y : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] (j : Y ⟶ X), IsOpenImmersion j → (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ L : LB Y, L.IsLB → ∃ L' : LB X, L'.IsLB ∧ ∃ φ : LB.Iso (L'.pull j) L, φ.IsGen) → Semi.extend_existsSt.{0} := by
  intro hint hreg hufd hext V _ _ _ K _ _ _ G _ _ _ _ _ _ eA _ L hL _ _
  have hV : IsRegularRing V := isRegularRing_of_isDiscreteValuationRing V
  have : GeometricallyIntegral G.hom := hint _ _ _ inferInstance inferInstance
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have := isOpenImmersion_etaK V K
  have hj : IsOpenImmersion (jA V K G) := inferInstance
  have hst : ∀ x : G.left, UniqueFactorizationMonoid (G.left.presheaf.stalk x) := fun x =>
    have := isRegularRing_stalk hreg V G.hom x
    hufd _
  obtain ⟨L', hL', φ, hφ⟩ := hext G.left _ (jA V K G) hj hst L hL
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := V) L' hL' (K := PUnit)
    (fun _ => eSec G) (fun _ => 1)
  exact ⟨⟨L', e, hL', he⟩, φ, hφ⟩

end GlobalTheory.ExtendRig
