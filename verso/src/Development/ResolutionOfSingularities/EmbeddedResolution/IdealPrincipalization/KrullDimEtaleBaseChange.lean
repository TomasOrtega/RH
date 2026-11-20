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

/- English proof (translation)
Rewrite using `[krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, h]`.
-/
theorem krullDimSucc_eq_of_topologicalKrullDim_eq {V P : Scheme.{u}}
    (h : topologicalKrullDim ↥V = topologicalKrullDim ↥P) :
    krullDimSucc V = krullDimSucc P := by
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, h]

/- English proof (translation)
Establish `: IsIso (Scheme.Hom.stalkMap U.ι x)` using `inferInstance`. Conclude with `(ringKrullDim_eq_of_ringEquiv (asIso (Scheme.Hom.stalkMap U.ι x)).commRingCatIsoToRingEquiv).symm`.
-/
theorem ringKrullDim_stalk_opens (X : Scheme.{u}) (U : X.Opens) (x : U.toScheme) :
    ringKrullDim (U.toScheme.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk (U.ι.base x)) := by
  have : IsIso (Scheme.Hom.stalkMap U.ι x) := inferInstance
  exact (ringKrullDim_eq_of_ringEquiv
    (asIso (Scheme.Hom.stalkMap U.ι x)).commRingCatIsoToRingEquiv).symm

/- English proof (translation)
Establish `: IsIso (Scheme.Hom.stalkMap U.ι y)` using `inferInstance`. Use `h` as an intermediate fact. Conclude with `isNoetherianRing_of_ringEquiv _ (asIso (Scheme.Hom.stalkMap U.ι y)).commRingCatIsoToRingEquiv`.
-/
private theorem isNoetherianRing_stalk_of_opens {X : Scheme.{u}} (U : X.Opens)
    (y : U.toScheme) (h : IsNoetherianRing (X.presheaf.stalk (U.ι.base y))) :
    IsNoetherianRing (U.toScheme.presheaf.stalk y) := by
  have : IsIso (Scheme.Hom.stalkMap U.ι y) := inferInstance
  have := h
  exact isNoetherianRing_of_ringEquiv _
    (asIso (Scheme.Hom.stalkMap U.ι y)).commRingCatIsoToRingEquiv

/- English proof (translation)
Use `c.isEtale` as an intermediate fact. Establish `: IsNoetherianRing (U.toScheme.presheaf.stalk (⟨x, hx⟩ : U.toScheme))` using `isNoetherianRing_stalk_of_opens U _ inferInstance`. Establish `h1 : ringKrullDim (U.toScheme.presheaf.stalk (⟨x, hx⟩ : U.toScheme)) ≤ ((m : ℕ∞) : WithBot ℕ∞)` using `ringKrullDim_stalk_le_of_etale_affineSpace c.map (⟨x, hx⟩ : U.toScheme)`. Rewrite `h1` using `[ringKrullDim_stalk_opens X U (⟨x, hx⟩ : U.toScheme)]`. Conclude with `h1`.
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

/- English proof (translation)
Take `⟨x, hx, hcl⟩` from `exists_mem_isClosed_singleton_of_isAffineOpen U hU hne`. Establish `: IsAffine U.toScheme` using `hU`. Use `c.isEtale` as an intermediate fact. Establish `: IsNoetherianRing (U.toScheme.presheaf.stalk (⟨x, hx⟩ : U.toScheme))` using `isNoetherianRing_stalk_of_opens U _ inferInstance`. Establish `h1 : ringKrullDim (U.toScheme.presheaf.stalk (⟨x, hx⟩ : U.toScheme)) = ((m : ℕ∞) : WithBot ℕ∞)` using `ringKrullDim_stalk_eq_of_etale_affineSpace c.map (⟨x, hx⟩ : U.toScheme) hcl`.

Establish `h2` using `ringKrullDim_stalk_opens X U (⟨x, hx⟩ : U.toScheme)`. Establish `h3` using `ringKrullDim_stalk_le_topologicalKrullDim X (U.ι.base (⟨x, hx⟩ : U.toScheme))`. Combine the equalities or inequalities in the displayed calculation.
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

/- English proof (translation)
Establish `: Algebra.FormallyUnramified D (FractionRing D)` using `Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors D)`. Establish `: Algebra.EssFiniteType D (FractionRing D)` using `Algebra.EssFiniteType.of_isLocalization (FractionRing D) (nonZeroDivisors D)`. Establish `: Algebra.FormallyUnramified K (FractionRing D)` using `Algebra.FormallyUnramified.comp K D (FractionRing D)`. Establish `: Algebra.EssFiniteType K (FractionRing D)` using `Algebra.EssFiniteType.comp K D (FractionRing D)`. Establish `: Algebra.IsSeparable K (FractionRing D)` using `(Algebra.FormallyUnramified.iff_isSeparable K (FractionRing D)).mp inferInstance`.

Establish `: Algebra.IsIntegral K D` using `⟨fun y => (Algebra.IsSeparable.isIntegral K (algebraMap D (FractionRing D) y)).tower_bot (IsFractionRing.injective D (FractionRing D))⟩`. Conclude with `isField_of_isIntegral_of_isField' (Field.toIsField K)`.
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

/- English proof (translation)
Use `hp` as an intermediate fact. Use `hQ` as an intermediate fact. Establish `: IsDomain (R ⧸ p)` using `Ideal.Quotient.isDomain p`. Take `⟨M, hMdef⟩ : ∃ M : Submonoid D, M = Submonoid.map (algebraMap R D) p.primeCompl` from `⟨_, rfl⟩`. Establish `hmemM : ∀ r : R, r ∈ p.primeCompl → algebraMap R D r ∈ M`.

Introduce `r hr`. Rewrite using `[hMdef]`. Conclude with `Submonoid.mem_map.mpr ⟨r, hr, rfl⟩`. Establish `hMle : M ≤ nonZeroDivisors D`. Introduce `z hz`.

Rewrite `hz` using `[hMdef]`. Take `⟨r, hr, rfl⟩` from `Submonoid.mem_map.mp hz`. Use `mem_nonZeroDivisors_of_ne_zero ?_` and prove the remaining obligations. Introduce `h0`. Conclude with `hr ((hker r).mp h0)`.

Establish `: IsDomain (Localization M)` using `IsLocalization.isDomain_of_le_nonZeroDivisors (Localization M) hMle`. Establish `: Algebra.FormallyUnramified D (Localization M)` using `Algebra.FormallyUnramified.of_isLocalization M`. Establish `: Algebra.EssFiniteType D (Localization M)` using `Algebra.EssFiniteType.of_isLocalization (Localization M) M`. Establish `: Algebra.FormallyUnramified R (Localization M)` using `Algebra.FormallyUnramified.comp R D (Localization M)`. Establish `: Algebra.EssFiniteType R (Localization M)` using `Algebra.EssFiniteType.comp R D (Localization M)`.

Establish `hzero : ∀ a : R, a ∈ p → algebraMap R (Localization M) a = 0`. Introduce `a ha`. Rewrite using `[IsScalarTower.algebraMap_apply R D (Localization M) a, (hker a).mpr ha, map_zero]`. Establish `hunits : ∀ z : nonZeroDivisors (R ⧸ p), IsUnit (Ideal.Quotient.lift p (algebraMap R (Localization M)) hzero (z : R ⧸ p))`. Introduce and unpack `⟨z, hz⟩`.

Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Establish `hne : (Ideal.Quotient.mk p r) ≠ 0` using `nonZeroDivisors.ne_zero hz`. Establish `hrp : r ∈ p.primeCompl` using `fun hmem => hne (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)`. Establish `h1 : Ideal.Quotient.lift p (algebraMap R (Localization M)) hzero (Ideal.Quotient.mk p r) = algebraMap D (Localization M) (algebraMap R D r)`. Rewrite using `[Ideal.Quotient.lift_mk, IsScalarTower.algebraMap_apply R D (Localization M) r]`.

Rewrite using `[h1]`. Conclude with `IsLocalization.map_units (Localization M) ⟨algebraMap R D r, hmemM r hrp⟩`. Set `_ : Algebra (FractionRing (R ⧸ p)) (Localization M)` to `RingHom.toAlgebra (IsLocalization.lift hunits : FractionRing (R ⧸ p) →+* Localization M)`. Establish `: IsScalarTower R (FractionRing (R ⧸ p)) (Localization M)`. Use `IsScalarTower.of_algebraMap_eq (fun r => ?_)` and prove the remaining obligations.

Establish `h3 : algebraMap R (FractionRing (R ⧸ p)) r = algebraMap (R ⧸ p) (FractionRing (R ⧸ p)) (Ideal.Quotient.mk p r)` using `IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p)) r`. Rewrite using `[h3, RingHom.algebraMap_toAlgebra, IsLocalization.lift_eq, Ideal.Quotient.lift_mk]`. Establish `: Algebra.EssFiniteType (FractionRing (R ⧸ p)) (Localization M)` using `Algebra.EssFiniteType.of_comp R (FractionRing (R ⧸ p)) (Localization M)`. Establish `: Algebra.FormallyUnramified (FractionRing (R ⧸ p)) (Localization M)`. Apply `Algebra.FormallyUnramified.of_restrictScalars (R := R)` to reduce the goal to its premises.

Establish `hfield : IsField (Localization M)` using `isField_of_formallyUnramified (FractionRing (R ⧸ p)) (Localization M)`. Assume the negation of the conclusion as `hQne`. Choose the witnesses or unpack the hypotheses as in `⟨y, hyQ, hy0⟩ : ∃ y ∈ Q, y ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Conclude with `hQne ((Submodule.eq_bot_iff Q).mpr hcon)`. Establish `hdisj : Disjoint (M : Set D) ((Q : Set D))`. Rewrite using `[Set.disjoint_left]`. Introduce `z hzM hzQ`. Rewrite `hzM` using `[hMdef]`.

Take `⟨r, hr, rfl⟩` from `Submonoid.mem_map.mp hzM`. Conclude with `hr (hQc r hzQ)`. Establish `hQP : (Q.map (algebraMap D (Localization M))).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint M (Localization M) Q hQ hdisj`. Establish `hyL : algebraMap D (Localization M) y ≠ 0`. Introduce `h0`.

Use `hy0 (IsLocalization.injective (Localization M) hMle ?_)` and prove the remaining obligations. Rewrite using `[h0, map_zero]`. Take `⟨z, hz⟩` from `hfield.mul_inv_cancel hyL`. Establish `hmem : algebraMap D (Localization M) y ∈ Q.map (algebraMap D (Localization M))` using `Ideal.mem_map_of_mem _ hyQ`. Establish `hone : (1 : Localization M) ∈ Q.map (algebraMap D (Localization M))`.

Rewrite using `[← hz]`. Conclude with `Ideal.mul_mem_right z _ hmem`. Conclude with `hQP.ne_top ((Ideal.eq_top_iff_one _).mpr hone)`.
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

/- English proof (translation)
Use `hq` as an intermediate fact. Use `hq'` as an intermediate fact. Establish `: IsDomain (S ⧸ q)` using `Ideal.Quotient.isDomain q`. Establish `: Algebra.FormallyUnramified R (S ⧸ q)` using `Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ R q) Ideal.Quotient.mk_surjective`. Establish `: Algebra.EssFiniteType S (S ⧸ q)` using `Algebra.EssFiniteType.of_surjective (Ideal.Quotient.mkₐ S q) Ideal.Quotient.mk_surjective`.

Establish `: Algebra.EssFiniteType R (S ⧸ q)` using `Algebra.EssFiniteType.comp R S (S ⧸ q)`. Establish `hmk : ∀ r : R, algebraMap R (S ⧸ q) r = Ideal.Quotient.mk q (algebraMap R S r)` using `fun r => IsScalarTower.algebraMap_apply R S (S ⧸ q) r`. Establish `hQ : (q'.map (Ideal.Quotient.mk q)).IsPrime`. Use `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective ?_` and prove the remaining obligations. Rewrite using `[Ideal.mk_ker]`.

Conclude with `hle`. Establish `hbot : q'.map (Ideal.Quotient.mk q) = ⊥`. Use `eq_bot_of_formallyUnramified_of_comap_le R (S ⧸ q) (q.comap (algebraMap R S)) inferInstance ?_ (q'.map (Ideal.Quotient.mk q)) hQ ?_` and prove the remaining obligations. Introduce `r`. Rewrite using `[hmk r, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Iff.rfl`. Introduce `r hr`. Rewrite `hr` using `[hmk r]`. Establish `hmem : algebraMap R S r ∈ q'` using `(Ideal.mem_quotient_iff_mem hle).mp hr`. Rewrite using `[hc]`.

Conclude with `hmem`. Use `le_antisymm hle ?_` and prove the remaining obligations. Introduce `z hz`. Establish `hzz : Ideal.Quotient.mk q z ∈ q'.map (Ideal.Quotient.mk q)` using `Ideal.mem_map_of_mem _ hz`. Rewrite `hzz` using `[hbot]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp (Ideal.mem_bot.mp hzz)`.
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

/- English proof (translation)
Introduce `a b hab`. Establish `hle : a.asIdeal ≤ b.asIdeal` using `hab.le`. Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations. Conclude with `Ideal.comap_mono hle`. Introduce `heq`.

Use `absurd ?_ (ne_of_lt hab)` and prove the remaining obligations. Conclude with `PrimeSpectrum.ext (eq_of_le_of_comap_eq R S a.asIdeal b.asIdeal a.isPrime b.isPrime hle (congrArg PrimeSpectrum.asIdeal heq))`.
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

/- English proof (translation)
Conclude with `Order.krullDim_le_of_strictMono _ (strictMono_comap_of_formallyUnramified R S)`.
-/
theorem ringKrullDim_le_of_essFiniteType_formallyUnramified (R : Type v) (S : Type w)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  exact Order.krullDim_le_of_strictMono _ (strictMono_comap_of_formallyUnramified R S)

/- English proof (translation)
Set `_ : Algebra A B` to `φ.toAlgebra`. Set `_ : Algebra A R` to `gA.toAlgebra`. Set `_ : Algebra B S` to `gB.toAlgebra`. Set `_ : Algebra R S` to `ψ.toAlgebra`. Set `_ : Algebra A S` to `(gB.comp φ).toAlgebra`.

Establish `: IsLocalization MA R` using `hlocA`. Establish `: IsLocalization MB S` using `hlocB`. Establish `: Algebra.Etale A B` using `hφ`. Establish `: IsLocalHom (algebraMap R S)` using `hlocal`. Establish `: IsScalarTower A B S` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Establish `: IsScalarTower A R S` using `IsScalarTower.of_algebraMap_eq fun a => (hcomm a).symm`. Establish `: Algebra.FormallyUnramified A B` using `inferInstance`. Establish `: Algebra.FiniteType A B` using `inferInstance`. Establish `: Algebra.EssFiniteType A B` using `inferInstance`. Establish `: Algebra.FormallyUnramified B S` using `Algebra.FormallyUnramified.of_isLocalization (M := MB)`.

Establish `: Algebra.EssFiniteType B S` using `Algebra.EssFiniteType.of_isLocalization S MB`. Establish `: Algebra.FormallyUnramified A S` using `Algebra.FormallyUnramified.comp A B S`. Establish `: Algebra.EssFiniteType A S` using `Algebra.EssFiniteType.comp A B S`. Establish `: Algebra.FormallyUnramified R S` using `Algebra.FormallyUnramified.localization_base MA`. Establish `: Algebra.EssFiniteType R S` using `Algebra.EssFiniteType.of_comp A R S`.

Conclude with `ringKrullDim_le_of_essFiniteType_formallyUnramified R S`.
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

/- English proof (translation)
Establish `hf : AlgebraicGeometry.Etale f` using `inferInstance`. Take `⟨U, hxU, hU⟩` from `Scheme.exists_isAffineOpen_mem (X := W) (f.base y)`. Take `⟨V₀, hyV₀, hV₀⟩` from `Scheme.exists_isAffineOpen_mem (X := Y) y`. Establish `hymem : y ∈ (V₀ ⊓ f ⁻¹ᵁ U : Y.Opens)` using `⟨hyV₀, hxU⟩`. Take `⟨g, hgle, hyg⟩` from `hV₀.exists_basicOpen_le (⟨y, hymem⟩ : (V₀ ⊓ f ⁻¹ᵁ U : Y.Opens)) hyV₀`.

Establish `hV : IsAffineOpen (Y.basicOpen g)` using `hV₀.basicOpen g`. Establish `hVU : Y.basicOpen g ≤ f ⁻¹ᵁ U` using `le_trans hgle inf_le_right`. Establish `hyV : y ∈ Y.basicOpen g` using `hyg`. Establish `hgerm : f.appLE U (Y.basicOpen g) hVU ≫ Y.presheaf.germ (Y.basicOpen g) y hyV = W.presheaf.germ U (f.base y) hxU ≫ f.stalkMap y`. Simplify using `[Scheme.Hom.appLE]`.

Establish `hetale : RingHom.Etale (f.appLE U (Y.basicOpen g) hVU).hom` using `AlgebraicGeometry.HasRingHomProperty.appLE (P := @AlgebraicGeometry.Etale) f hf ⟨U, hU⟩ ⟨Y.basicOpen g, hV⟩ hVU`. Use `ringKrullDim_le_of_isLocalization_etale (f.appLE U (Y.basicOpen g) hVU).hom (W.presheaf.germ U (f.base y) hxU).hom (Y.presheaf.germ (Y.basicOpen g) y hyV).hom (f.stalkMap y).hom (hU.primeIdealOf ⟨f.base y, hxU⟩).asIdeal.primeCompl (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl het …` and prove the remaining obligations. Conclude with `congrArg (fun t : Γ(W, U) ⟶ Y.presheaf.stalk y => t.hom a) hgerm.symm`.
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

/- English proof (translation)
Establish `: AlgebraicGeometry.IsLocallyNoetherian V` using `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f`. Use `topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le V (topologicalKrullDim ↥P) ?_` and prove the remaining obligations. Introduce `y`. Establish `: IsNoetherianRing (V.presheaf.stalk y)` using `inferInstance`. Establish `: IsNoetherianRing (P.presheaf.stalk (f.base y))` using `inferInstance`.

Conclude with `le_trans (ringKrullDim_stalk_le_of_etale_of_isNoetherianRing f y) (ringKrullDim_stalk_le_topologicalKrullDim P (f.base y))`.
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

/- English proof (translation)
The claim follows from `krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le _ _ (topologicalKrullDim_le_of_etale f) hP`.
-/
theorem krullDimSucc_le_of_etale {V P : Scheme.{u}} (f : V ⟶ P)
    [AlgebraicGeometry.Etale f] [AlgebraicGeometry.IsLocallyNoetherian P]
    (hP : topologicalKrullDim ↥P < ⊤) :
    krullDimSucc V ≤ krullDimSucc P :=
  krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le _ _ (topologicalKrullDim_le_of_etale f) hP

/- English proof (translation)
Use `⟨fun U => ?_⟩` and prove the remaining obligations. Conclude with `@isNoetherianRing_sections k _ _ P pP _ U (sectionsAlgebra k pP U.1) (algebraMap_sectionsAlgebra k pP U.1)`.
-/
private theorem isLocallyNoetherian_of_smooth_over_field {k : Type u} [Field k]
    {P : Scheme.{u}} (pP : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth pP] :
    AlgebraicGeometry.IsLocallyNoetherian P := by
  refine ⟨fun U => ?_⟩
  exact @isNoetherianRing_sections k _ _ P pP _ U (sectionsAlgebra k pP U.1)
    (algebraMap_sectionsAlgebra k pP U.1)

/- English proof (translation)
Establish `hsq` using `isPullback_pullback_specMap p (CommRingCat.ofHom f)`. Establish `hS : AlgebraicGeometry.Surjective (specMapOfFieldHom k K f)` using `FunctorialResolution.EmbeddedResolution.instSurjectiveSpecMapOfFieldHom k K f`. Establish `: AlgebraicGeometry.Surjective (pullback.fst p (specMapOfFieldHom k K f))` using `MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @AlgebraicGeometry.Surjective) hsq hS`. Conclude with `Scheme.Hom.surjective _`.
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

/- English proof (translation)
Establish `: AlgebraicGeometry.IsLocallyNoetherian X` using `isLocallyNoetherian_of_smooth_over_field p`. Establish `: AlgebraicGeometry.IsLocallyNoetherian (pullback p (Spec.map φ))` using `isLocallyNoetherian_of_smooth_over_field (pullback.snd p (Spec.map φ))`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Use `topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le _ _ ?_` and prove the remaining obligations. Introduce `y`.

Take `⟨U, m, hxU, hU, ⟨c⟩⟩` from `exists_etaleChart p ((pullback.fst p (Spec.map φ)).base y)`. Take `⟨V, -, c', -, hyV, -⟩` from `exists_etaleChart_pullback_specMap p φ c y hxU`. Conclude with `le_trans (ringKrullDim_stalk_le_of_etaleChart_of_isLocallyNoetherian (pullback.snd p (Spec.map φ)) c' y hyV) (etaleChart_dim_le_topologicalKrullDim p c hU ⟨(pullback.fst p (Spec.map φ)).base y, hxU⟩)`. Use `topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le _ _ ?_` and prove the remaining obligations. Introduce `x`.

Take `⟨U, m, hxU, hU, ⟨c⟩⟩` from `exists_etaleChart p x`. Take `⟨y, rfl⟩` from `hsurj x`. Take `⟨V, -, c', hVaff, hyV, -⟩` from `exists_etaleChart_pullback_specMap p φ c y hxU`. Conclude with `le_trans (ringKrullDim_stalk_le_of_etaleChart_of_isLocallyNoetherian p c _ hxU) (etaleChart_dim_le_topologicalKrullDim (pullback.snd p (Spec.map φ)) c' hVaff ⟨y, hyV⟩)`.
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

/- English proof (translation)
The claim follows from `topologicalKrullDim_pullback_spec_map_of_surjective p (CommRingCat.ofHom f) (surjective_base_pullback_fst_specMapOfFieldHom p f)`.
-/
theorem topologicalKrullDim_pullback_specMapOfFieldHom {k K : Type u} [Field k] [Field K]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (f : k →+* K) :
    topologicalKrullDim ↥(pullback p (specMapOfFieldHom k K f)) = topologicalKrullDim ↥X :=
  topologicalKrullDim_pullback_spec_map_of_surjective p (CommRingCat.ofHom f)
    (surjective_base_pullback_fst_specMapOfFieldHom p f)

/- English proof (translation)
Establish `: AlgebraicGeometry.Smooth T.structMap` using `hT.smooth`. Establish `h : topologicalKrullDim ↥(T.baseChange L f).scheme = topologicalKrullDim ↥T.scheme` using `topologicalKrullDim_pullback_specMapOfFieldHom T.structMap f`. Conclude with `krullDimSucc_eq_of_topologicalKrullDim_eq h`.
-/
theorem MarkedIdealWithBoundary.dim_baseChange (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (L : Type u) [Field L]
    [CharZero L] (f : T.base →+* L) :
    (T.baseChange L f).krullDimSucc = T.krullDimSucc := by
  have : AlgebraicGeometry.Smooth T.structMap := hT.smooth
  have h : topologicalKrullDim ↥(T.baseChange L f).scheme = topologicalKrullDim ↥T.scheme :=
    topologicalKrullDim_pullback_specMapOfFieldHom T.structMap f
  exact krullDimSucc_eq_of_topologicalKrullDim_eq h

end FunctorialResolution.EmbeddedResolution
