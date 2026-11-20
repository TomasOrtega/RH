import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StalkKrullDimension
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.Foundations.Schemes.AffineOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FiniteKrullDim
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The dimension index is the same successor conversion of topological Krull dimension for both schemes. Applying that conversion to the given equality gives equal indices.
-/
theorem krullDimSucc_eq_of_topologicalKrullDim_eq {V P : Scheme.{u}}
    (h : topologicalKrullDim ↥V = topologicalKrullDim ↥P) :
    krullDimSucc V = krullDimSucc P := by
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, h]

/- English proof (authored)
The inclusion of an open subscheme induces an isomorphism of the local rings at corresponding points. Isomorphic rings have the same Krull dimension.
-/
theorem ringKrullDim_stalk_opens (X : Scheme.{u}) (U : X.Opens) (x : U.toScheme) :
    ringKrullDim (U.toScheme.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk (U.ι.base x)) := by
  have : IsIso (Scheme.Hom.stalkMap U.ι x) := inferInstance
  exact (ringKrullDim_eq_of_ringEquiv
    (asIso (Scheme.Hom.stalkMap U.ι x)).commRingCatIsoToRingEquiv).symm

/- English proof (authored)
The stalk map of an open inclusion is a ring isomorphism. It transfers Noetherianity of the ambient local ring to the local ring on the open.
-/
private theorem isNoetherianRing_stalk_of_opens {X : Scheme.{u}} (U : X.Opens)
    (y : U.toScheme) (h : IsNoetherianRing (X.presheaf.stalk (U.ι.base y))) :
    IsNoetherianRing (U.toScheme.presheaf.stalk y) := by
  have : IsIso (Scheme.Hom.stalkMap U.ι y) := inferInstance
  have := h
  exact isNoetherianRing_of_ringEquiv _
    (asIso (Scheme.Hom.stalkMap U.ι y)).commRingCatIsoToRingEquiv

/- English proof (authored)
The local ring of the chart domain is Noetherian because it is isomorphic to the ambient local ring. An étale morphism to affine space bounds the dimension of that local ring by the number of coordinates. Transfer the bound to the ambient local ring through the open-inclusion isomorphism.
-/
theorem ringKrullDim_stalk_le_of_etaleChart_of_isLocallyNoetherian {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.IsLocallyNoetherian X]
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (x : X) (hx : x ∈ U) :
    ringKrullDim (X.presheaf.stalk x) ≤ ((m : ℕ∞) : WithBot ℕ∞) := by
  have := c.isEtale
  have : IsNoetherianRing (U.toScheme.presheaf.stalk (⟨x, hx⟩ : U.toScheme)) :=
    isNoetherianRing_stalk_of_opens U _ inferInstance
  have h1 : ringKrullDim (U.toScheme.presheaf.stalk (⟨x, hx⟩ : U.toScheme))
      ≤ ((m : ℕ∞) : WithBot ℕ∞) :=
    ringKrullDim_stalk_le_of_etale_affineSpace c.map (⟨x, hx⟩ : U.toScheme)
  rw [ringKrullDim_stalk_opens X U (⟨x, hx⟩ : U.toScheme)] at h1
  exact h1

/- English proof (authored)
Choose a closed point of the nonempty affine chart. At that point the local ring is Noetherian, and the local dimension theorem for an étale chart identifies its dimension with the number of coordinates. That local ring agrees with the ambient local ring at the same point. The dimension of any ambient local ring is at most the topological dimension of the scheme, giving the bound.
-/
theorem etaleChart_dim_le_topologicalKrullDim {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.IsLocallyNoetherian X]
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (hU : IsAffineOpen U)
    (hne : (U : Set ↥X).Nonempty) :
    ((m : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim ↥X := by
  obtain ⟨x, hx, hcl⟩ := exists_mem_isClosed_singleton_of_isAffineOpen U hU hne
  have : IsAffine U.toScheme := hU
  have := c.isEtale
  have : IsNoetherianRing (U.toScheme.presheaf.stalk (⟨x, hx⟩ : U.toScheme)) :=
    isNoetherianRing_stalk_of_opens U _ inferInstance
  have h1 : ringKrullDim (U.toScheme.presheaf.stalk (⟨x, hx⟩ : U.toScheme))
      = ((m : ℕ∞) : WithBot ℕ∞) :=
    ringKrullDim_stalk_eq_of_etale_affineSpace c.map (⟨x, hx⟩ : U.toScheme) hcl
  have h2 := ringKrullDim_stalk_opens X U (⟨x, hx⟩ : U.toScheme)
  have h3 := ringKrullDim_stalk_le_topologicalKrullDim X (U.ι.base (⟨x, hx⟩ : U.toScheme))
  calc ((m : ℕ∞) : WithBot ℕ∞)
      = ringKrullDim (U.toScheme.presheaf.stalk (⟨x, hx⟩ : U.toScheme)) := h1.symm
    _ = ringKrullDim (X.presheaf.stalk (U.ι.base (⟨x, hx⟩ : U.toScheme))) := h2
    _ ≤ topologicalKrullDim ↥X := h3

/- English proof (authored)
Pass from the domain to its fraction field. Localization is formally unramified and essentially of finite type, and both properties are preserved by composition over the base field. For this field extension formal unramifiedness gives separability, hence algebraicity. Every element of the domain is then integral over the base field because the domain embeds in its fraction field. A domain integral over a field is a field.
-/
private theorem isField_of_formallyUnramified (K : Type v) (D : Type w) [Field K]
    [CommRing D] [IsDomain D] [Algebra K D] [Algebra.EssFiniteType K D]
    [Algebra.FormallyUnramified K D] : IsField D := by
  have : Algebra.FormallyUnramified D (FractionRing D) :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors D)
  have : Algebra.EssFiniteType D (FractionRing D) :=
    Algebra.EssFiniteType.of_isLocalization (FractionRing D) (nonZeroDivisors D)
  have : Algebra.FormallyUnramified K (FractionRing D) :=
    Algebra.FormallyUnramified.comp K D (FractionRing D)
  have : Algebra.EssFiniteType K (FractionRing D) :=
    Algebra.EssFiniteType.comp K D (FractionRing D)
  have : Algebra.IsSeparable K (FractionRing D) :=
    (Algebra.FormallyUnramified.iff_isSeparable K (FractionRing D)).mp inferInstance
  have : Algebra.IsIntegral K D :=
    ⟨fun y => (Algebra.IsSeparable.isIntegral K (algebraMap D (FractionRing D) y)).tower_bot
      (IsFractionRing.injective D (FractionRing D))⟩
  exact isField_of_isIntegral_of_isField' (Field.toIsField K)

/- English proof (authored)
Localize the target domain at the images of elements outside the kernel prime of the base. These images are nonzero, so the localization remains a domain and the localization map is injective. The base map to the localization kills the kernel prime and inverts every nonzero class modulo that prime. It therefore factors through the fraction field of the quotient base. The localized domain is essentially of finite type and formally unramified over that field by the corresponding composition and restriction properties. It is consequently a field.

The prime in the statement avoids the inverted elements because its contraction is contained in the kernel prime. It therefore extends to a proper prime in the localization. If it contained a nonzero element, that element would remain nonzero by injectivity and become a unit in the field. This would put one in the extended prime, a contradiction. Thus the original prime is zero.
-/
private theorem eq_bot_of_formallyUnramified_of_comap_le (R : Type v) (D : Type w) [CommRing R]
    [CommRing D] [IsDomain D] [Algebra R D] [Algebra.EssFiniteType R D]
    [Algebra.FormallyUnramified R D]
    (p : Ideal R) (hp : p.IsPrime) (hker : ∀ r : R, algebraMap R D r = 0 ↔ r ∈ p)
    (Q : Ideal D) (hQ : Q.IsPrime) (hQc : ∀ r : R, algebraMap R D r ∈ Q → r ∈ p) :
    Q = ⊥ := by
  have := hp
  have := hQ
  have : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
  obtain ⟨M, hMdef⟩ : ∃ M : Submonoid D, M = Submonoid.map (algebraMap R D) p.primeCompl :=
    ⟨_, rfl⟩
  have hmemM : ∀ r : R, r ∈ p.primeCompl → algebraMap R D r ∈ M := by
    intro r hr
    rw [hMdef]
    exact Submonoid.mem_map.mpr ⟨r, hr, rfl⟩
  have hMle : M ≤ nonZeroDivisors D := by
    intro z hz
    rw [hMdef] at hz
    obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.mp hz
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    exact hr ((hker r).mp h0)
  have : IsDomain (Localization M) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization M) hMle
  have : Algebra.FormallyUnramified D (Localization M) :=
    Algebra.FormallyUnramified.of_isLocalization M
  have : Algebra.EssFiniteType D (Localization M) :=
    Algebra.EssFiniteType.of_isLocalization (Localization M) M
  have : Algebra.FormallyUnramified R (Localization M) :=
    Algebra.FormallyUnramified.comp R D (Localization M)
  have : Algebra.EssFiniteType R (Localization M) :=
    Algebra.EssFiniteType.comp R D (Localization M)
  have hzero : ∀ a : R, a ∈ p → algebraMap R (Localization M) a = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply R D (Localization M) a, (hker a).mpr ha, map_zero]
  have hunits : ∀ z : nonZeroDivisors (R ⧸ p),
      IsUnit (Ideal.Quotient.lift p (algebraMap R (Localization M)) hzero (z : R ⧸ p)) := by
    rintro ⟨z, hz⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hne : (Ideal.Quotient.mk p r) ≠ 0 := nonZeroDivisors.ne_zero hz
    have hrp : r ∈ p.primeCompl := fun hmem => hne (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
    have h1 : Ideal.Quotient.lift p (algebraMap R (Localization M)) hzero
        (Ideal.Quotient.mk p r) = algebraMap D (Localization M) (algebraMap R D r) := by
      rw [Ideal.Quotient.lift_mk, IsScalarTower.algebraMap_apply R D (Localization M) r]
    rw [h1]
    exact IsLocalization.map_units (Localization M) ⟨algebraMap R D r, hmemM r hrp⟩
  let _ : Algebra (FractionRing (R ⧸ p)) (Localization M) :=
    RingHom.toAlgebra (IsLocalization.lift hunits : FractionRing (R ⧸ p) →+* Localization M)
  have : IsScalarTower R (FractionRing (R ⧸ p)) (Localization M) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    have h3 : algebraMap R (FractionRing (R ⧸ p)) r
        = algebraMap (R ⧸ p) (FractionRing (R ⧸ p)) (Ideal.Quotient.mk p r) :=
      IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p)) r
    rw [h3, RingHom.algebraMap_toAlgebra, IsLocalization.lift_eq, Ideal.Quotient.lift_mk]
  have : Algebra.EssFiniteType (FractionRing (R ⧸ p)) (Localization M) :=
    Algebra.EssFiniteType.of_comp R (FractionRing (R ⧸ p)) (Localization M)
  have : Algebra.FormallyUnramified (FractionRing (R ⧸ p)) (Localization M) := by
    apply Algebra.FormallyUnramified.of_restrictScalars (R := R)
  have hfield : IsField (Localization M) :=
    isField_of_formallyUnramified (FractionRing (R ⧸ p)) (Localization M)
  by_contra hQne
  obtain ⟨y, hyQ, hy0⟩ : ∃ y ∈ Q, y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hQne ((Submodule.eq_bot_iff Q).mpr hcon)
  have hdisj : Disjoint (M : Set D) ((Q : Set D)) := by
    rw [Set.disjoint_left]
    intro z hzM hzQ
    rw [hMdef] at hzM
    obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.mp hzM
    exact hr (hQc r hzQ)
  have hQP : (Q.map (algebraMap D (Localization M))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M (Localization M) Q hQ hdisj
  have hyL : algebraMap D (Localization M) y ≠ 0 := by
    intro h0
    refine hy0 (IsLocalization.injective (Localization M) hMle ?_)
    rw [h0, map_zero]
  obtain ⟨z, hz⟩ := hfield.mul_inv_cancel hyL
  have hmem : algebraMap D (Localization M) y ∈ Q.map (algebraMap D (Localization M)) :=
    Ideal.mem_map_of_mem _ hyQ
  have hone : (1 : Localization M) ∈ Q.map (algebraMap D (Localization M)) := by
    rw [← hz]
    exact Ideal.mul_mem_right z _ hmem
  exact hQP.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

/- English proof (authored)
Quotient the target by the smaller prime. The resulting domain is still essentially of finite type and formally unramified over the base. The kernel of the new base map is the contraction of the smaller prime. The image of the larger prime is prime in the quotient, and its contraction is contained in the kernel prime by the given equality of contractions. The domain result makes this image prime zero. Hence the larger prime lies in the smaller one and they are equal.
-/
private theorem eq_of_le_of_comap_eq (R : Type v) (S : Type w) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    (q q' : Ideal S) (hq : q.IsPrime) (hq' : q'.IsPrime) (hle : q ≤ q')
    (hc : q.comap (algebraMap R S) = q'.comap (algebraMap R S)) : q = q' := by
  have := hq
  have := hq'
  have : IsDomain (S ⧸ q) := Ideal.Quotient.isDomain q
  have : Algebra.FormallyUnramified R (S ⧸ q) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ R q) Ideal.Quotient.mk_surjective
  have : Algebra.EssFiniteType S (S ⧸ q) :=
    Algebra.EssFiniteType.of_surjective (Ideal.Quotient.mkₐ S q) Ideal.Quotient.mk_surjective
  have : Algebra.EssFiniteType R (S ⧸ q) := Algebra.EssFiniteType.comp R S (S ⧸ q)
  have hmk : ∀ r : R, algebraMap R (S ⧸ q) r = Ideal.Quotient.mk q (algebraMap R S r) :=
    fun r => IsScalarTower.algebraMap_apply R S (S ⧸ q) r
  have hQ : (q'.map (Ideal.Quotient.mk q)).IsPrime := by
    refine Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker]
    exact hle
  have hbot : q'.map (Ideal.Quotient.mk q) = ⊥ := by
    refine eq_bot_of_formallyUnramified_of_comap_le R (S ⧸ q) (q.comap (algebraMap R S))
      inferInstance ?_ (q'.map (Ideal.Quotient.mk q)) hQ ?_
    · intro r
      rw [hmk r, Ideal.Quotient.eq_zero_iff_mem]
      exact Iff.rfl
    · intro r hr
      rw [hmk r] at hr
      have hmem : algebraMap R S r ∈ q' := (Ideal.mem_quotient_iff_mem hle).mp hr
      rw [hc]
      exact hmem
  refine le_antisymm hle ?_
  intro z hz
  have hzz : Ideal.Quotient.mk q z ∈ q'.map (Ideal.Quotient.mk q) := Ideal.mem_map_of_mem _ hz
  rw [hbot] at hzz
  exact Ideal.Quotient.eq_zero_iff_mem.mp (Ideal.mem_bot.mp hzz)

/- English proof (authored)
Contraction preserves inclusion of primes. For a strict inclusion, equal contractions would force the two primes to be equal by the preceding prime comparison theorem. Thus contraction preserves strict inclusion.
-/
private theorem strictMono_comap_of_formallyUnramified (R : Type v) (S : Type w) [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro a b hab
  have hle : a.asIdeal ≤ b.asIdeal := hab.le
  refine lt_of_le_of_ne ?_ ?_
  · exact Ideal.comap_mono hle
  · intro heq
    refine absurd ?_ (ne_of_lt hab)
    exact PrimeSpectrum.ext (eq_of_le_of_comap_eq R S a.asIdeal b.asIdeal a.isPrime b.isPrime hle
      (congrArg PrimeSpectrum.asIdeal heq))

/- English proof (authored)
Every finite strict chain of target primes contracts to a strict chain of the same length by the contraction result. Taking the supremum of chain lengths gives the dimension bound.
-/
theorem ringKrullDim_le_of_essFiniteType_formallyUnramified (R : Type v) (S : Type w)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  exact Order.krullDim_le_of_strictMono _ (strictMono_comap_of_formallyUnramified R S)

/- English proof (authored)
The given étale ring map is finite type and formally unramified. Composing with localization of the target gives a map from the original source ring to the localized target that is essentially of finite type and formally unramified. The commutative diagram factors this map through the localized source. These two properties pass to that factor over the localized source by the localization and composition results. The dimension bound for essentially finite-type formally unramified maps now applies to the given local rings.
-/
private theorem ringKrullDim_le_of_isLocalization_etale {A B R S : Type u} [CommRing A]
    [CommRing B] [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [IsNoetherianRing S] (φ : A →+* B) (gA : A →+* R) (gB : B →+* S) (ψ : R →+* S)
    (MA : Submonoid A) (MB : Submonoid B) (hφ : RingHom.Etale φ)
    (hlocA : @IsLocalization A _ MA R _ gA.toAlgebra)
    (hlocB : @IsLocalization B _ MB S _ gB.toAlgebra)
    (hcomm : ∀ a : A, ψ (gA a) = gB (φ a)) (hlocal : IsLocalHom ψ) :
    ringKrullDim S ≤ ringKrullDim R := by
  let _ : Algebra A B := φ.toAlgebra
  let _ : Algebra A R := gA.toAlgebra
  let _ : Algebra B S := gB.toAlgebra
  let _ : Algebra R S := ψ.toAlgebra
  let _ : Algebra A S := (gB.comp φ).toAlgebra
  have : IsLocalization MA R := hlocA
  have : IsLocalization MB S := hlocB
  have : Algebra.Etale A B := hφ
  have : IsLocalHom (algebraMap R S) := hlocal
  have : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq fun a => (hcomm a).symm
  have : Algebra.FormallyUnramified A B := inferInstance
  have : Algebra.FiniteType A B := inferInstance
  have : Algebra.EssFiniteType A B := inferInstance
  have : Algebra.FormallyUnramified B S := Algebra.FormallyUnramified.of_isLocalization (M := MB)
  have : Algebra.EssFiniteType B S := Algebra.EssFiniteType.of_isLocalization S MB
  have : Algebra.FormallyUnramified A S := Algebra.FormallyUnramified.comp A B S
  have : Algebra.EssFiniteType A S := Algebra.EssFiniteType.comp A B S
  have : Algebra.FormallyUnramified R S := Algebra.FormallyUnramified.localization_base MA
  have : Algebra.EssFiniteType R S := Algebra.EssFiniteType.of_comp A R S
  exact ringKrullDim_le_of_essFiniteType_formallyUnramified R S

/- English proof (authored)
Choose an affine neighborhood of the target point and an affine neighborhood of the source point within its inverse image. The latter can be taken to be a basic open of an initial affine neighborhood. On sections the induced map is étale. The local rings are localizations of those section rings at the relevant primes, and the germ maps commute with the map on stalks. Apply the dimension inequality for localizations of an étale map.
-/
theorem ringKrullDim_stalk_le_of_etale_of_isNoetherianRing {Y W : Scheme.{u}} (f : Y ⟶ W)
    [AlgebraicGeometry.Etale f] (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    [IsNoetherianRing (W.presheaf.stalk (f.base y))] :
    ringKrullDim (Y.presheaf.stalk y) ≤ ringKrullDim (W.presheaf.stalk (f.base y)) := by
  have hf : AlgebraicGeometry.Etale f := inferInstance
  obtain ⟨U, hxU, hU⟩ := Scheme.exists_isAffineOpen_mem (X := W) (f.base y)
  obtain ⟨V₀, hyV₀, hV₀⟩ := Scheme.exists_isAffineOpen_mem (X := Y) y
  have hymem : y ∈ (V₀ ⊓ f ⁻¹ᵁ U : Y.Opens) := ⟨hyV₀, hxU⟩
  obtain ⟨g, hgle, hyg⟩ :=
    hV₀.exists_basicOpen_le (⟨y, hymem⟩ : (V₀ ⊓ f ⁻¹ᵁ U : Y.Opens)) hyV₀
  have hV : IsAffineOpen (Y.basicOpen g) := hV₀.basicOpen g
  have hVU : Y.basicOpen g ≤ f ⁻¹ᵁ U := le_trans hgle inf_le_right
  have hyV : y ∈ Y.basicOpen g := hyg
  have hgerm : f.appLE U (Y.basicOpen g) hVU ≫ Y.presheaf.germ (Y.basicOpen g) y hyV
      = W.presheaf.germ U (f.base y) hxU ≫ f.stalkMap y := by
    simp [Scheme.Hom.appLE]
  have hetale : RingHom.Etale (f.appLE U (Y.basicOpen g) hVU).hom :=
    AlgebraicGeometry.HasRingHomProperty.appLE (P := @AlgebraicGeometry.Etale) f hf
      ⟨U, hU⟩ ⟨Y.basicOpen g, hV⟩ hVU
  refine ringKrullDim_le_of_isLocalization_etale (f.appLE U (Y.basicOpen g) hVU).hom
    (W.presheaf.germ U (f.base y) hxU).hom
    (Y.presheaf.germ (Y.basicOpen g) y hyV).hom (f.stalkMap y).hom
    (hU.primeIdealOf ⟨f.base y, hxU⟩).asIdeal.primeCompl
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl hetale
    (hU.isLocalization_stalk ⟨f.base y, hxU⟩)
    (hV.isLocalization_stalk ⟨y, hyV⟩) (fun a => ?_) inferInstance
  exact congrArg (fun t : Γ(W, U) ⟶ Y.presheaf.stalk y => t.hom a) hgerm.symm

/- English proof (authored)
An étale morphism is locally of finite type, so its source is locally Noetherian because its target is. At each source point the dimension of the local ring is at most the dimension of the target local ring by the étale stalk bound. The latter is at most the topological dimension of the target. Bounding every source local ring in this way bounds the source's topological dimension.
-/
theorem topologicalKrullDim_le_of_etale {V P : Scheme.{u}} (f : V ⟶ P)
    [AlgebraicGeometry.Etale f] [AlgebraicGeometry.IsLocallyNoetherian P] :
    topologicalKrullDim ↥V ≤ topologicalKrullDim ↥P := by
  have : AlgebraicGeometry.IsLocallyNoetherian V :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f
  refine topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le V
    (topologicalKrullDim ↥P) ?_
  intro y
  have : IsNoetherianRing (V.presheaf.stalk y) := inferInstance
  have : IsNoetherianRing (P.presheaf.stalk (f.base y)) := inferInstance
  exact le_trans (ringKrullDim_stalk_le_of_etale_of_isNoetherianRing f y)
    (ringKrullDim_stalk_le_topologicalKrullDim P (f.base y))

/- English proof (authored)
The étale dimension inequality bounds the source by the target. Since the target dimension is finite, the conversion to successor indices preserves the weak inequality.
-/
theorem krullDimSucc_le_of_etale {V P : Scheme.{u}} (f : V ⟶ P)
    [AlgebraicGeometry.Etale f] [AlgebraicGeometry.IsLocallyNoetherian P]
    (hP : topologicalKrullDim ↥P < ⊤) :
    krullDimSucc V ≤ krullDimSucc P :=
  krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le _ _ (topologicalKrullDim_le_of_etale f) hP

/- English proof (authored)
Sections on each affine open of a smooth scheme over a field are a finite-type algebra over that field and hence Noetherian. This is the local Noetherian condition.
-/
private theorem isLocallyNoetherian_of_smooth_over_field {k : Type u} [Field k]
    {P : Scheme.{u}} (pP : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth pP] :
    AlgebraicGeometry.IsLocallyNoetherian P := by
  refine ⟨fun U => ?_⟩
  exact @isNoetherianRing_sections k _ _ P pP _ U (sectionsAlgebra k pP U.1)
    (algebraMap_sectionsAlgebra k pP U.1)

/- English proof (authored)
A field spectrum is a single point, so the map of field spectra is surjective. The projection in question is its base change, and surjectivity is preserved by base change.
-/
private theorem surjective_base_pullback_fst_specMapOfFieldHom {k K : Type u} [Field k] [Field K]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) (f : k →+* K) :
    Function.Surjective (pullback.fst p (specMapOfFieldHom k K f)).base := by
  have hsq := isPullback_pullback_specMap p (CommRingCat.ofHom f)
  have hS : AlgebraicGeometry.Surjective (specMapOfFieldHom k K f) :=
    FunctorialResolution.EmbeddedResolution.instSurjectiveSpecMapOfFieldHom k K f
  have : AlgebraicGeometry.Surjective (pullback.fst p (specMapOfFieldHom k K f)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Surjective) hsq hS
  exact Scheme.Hom.surjective _

/- English proof (authored)
The original and extended schemes are smooth over their fields, hence locally Noetherian. For a point of the extended scheme, choose an affine étale chart around its image and pull this chart back to the extended scheme. The extended local dimension is at most the chart's number of coordinates, which is at most the original scheme's dimension by the bound for nonempty affine charts. This bounds the extended scheme's dimension from above.

For the reverse direction, choose an affine étale chart at any point of the original scheme and use surjectivity to choose a point above it. The original local dimension is at most the number of chart coordinates. The extended chart has that same number and is nonempty and affine, so this number is at most the extended scheme's dimension. The bounds on all original local rings give the reverse inequality.
-/
private theorem topologicalKrullDim_pullback_spec_map_of_surjective {k K : Type u} [Field k] [Field K]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (φ : CommRingCat.of k ⟶ CommRingCat.of K)
    (hsurj : Function.Surjective (pullback.fst p (Spec.map φ)).base) :
    topologicalKrullDim ↥(pullback p (Spec.map φ)) = topologicalKrullDim ↥X := by
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    isLocallyNoetherian_of_smooth_over_field p
  have : AlgebraicGeometry.IsLocallyNoetherian (pullback p (Spec.map φ)) :=
    isLocallyNoetherian_of_smooth_over_field (pullback.snd p (Spec.map φ))
  refine le_antisymm ?_ ?_
  · refine topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le _ _ ?_
    intro y
    obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p ((pullback.fst p (Spec.map φ)).base y)
    obtain ⟨V, -, c', -, hyV, -⟩ := exists_etaleChart_pullback_specMap p φ c y hxU
    exact le_trans
      (ringKrullDim_stalk_le_of_etaleChart_of_isLocallyNoetherian (pullback.snd p (Spec.map φ)) c' y hyV)
      (etaleChart_dim_le_topologicalKrullDim p c hU
        ⟨(pullback.fst p (Spec.map φ)).base y, hxU⟩)
  · refine topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le _ _ ?_
    intro x
    obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
    obtain ⟨y, rfl⟩ := hsurj x
    obtain ⟨V, -, c', hVaff, hyV, -⟩ := exists_etaleChart_pullback_specMap p φ c y hxU
    exact le_trans (ringKrullDim_stalk_le_of_etaleChart_of_isLocallyNoetherian p c _ hxU)
      (etaleChart_dim_le_topologicalKrullDim (pullback.snd p (Spec.map φ)) c' hVaff ⟨y, hyV⟩)

/- English proof (authored)
The projection of the field base change is surjective by stability of surjectivity under base change. The dimension comparison for a smooth scheme with such a projection therefore gives equality.
-/
theorem topologicalKrullDim_pullback_specMapOfFieldHom {k K : Type u} [Field k] [Field K]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (f : k →+* K) :
    topologicalKrullDim ↥(pullback p (specMapOfFieldHom k K f)) = topologicalKrullDim ↥X :=
  topologicalKrullDim_pullback_spec_map_of_surjective p (CommRingCat.ofHom f)
    (surjective_base_pullback_fst_specMapOfFieldHom p f)

/- English proof (authored)
Admissibility makes the original structure map smooth. Extending the field preserves the ambient topological Krull dimension by the comparison for smooth schemes. Applying the common successor conversion gives equality of the marked ideals' dimension indices.
-/
theorem MarkedIdealWithBoundary.dim_baseChange (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (L : Type u) [Field L]
    [CharZero L] (f : T.base →+* L) :
    (T.baseChange L f).krullDimSucc = T.krullDimSucc := by
  have : AlgebraicGeometry.Smooth T.structMap := hT.smooth
  have h : topologicalKrullDim ↥(T.baseChange L f).scheme = topologicalKrullDim ↥T.scheme :=
    topologicalKrullDim_pullback_specMapOfFieldHom T.structMap f
  exact krullDimSucc_eq_of_topologicalKrullDim_eq h

end FunctorialResolution.EmbeddedResolution
