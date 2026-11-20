import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealLocalization
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealOrderDecrease
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

noncomputable def stalkAlgebraMap (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) : k →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x (Opens.mem_top x)).hom.comp (sectionsAlgebraMap k p ⊤)

@[reducible] noncomputable def stalkAlgebra (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) : Algebra k (X.presheaf.stalk x) :=
  (stalkAlgebraMap k p x).toAlgebra

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_stalkAlgebra (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    @algebraMap k (X.presheaf.stalk x) _ _ (stalkAlgebra k p x) = stalkAlgebraMap k p x :=
  rfl

/- English proof (translation)
Establish `hle : U ≤ (⊤ : X.Opens)` using `le_top`. Establish `key : X.presheaf.map (homOfLE hle).op ≫ X.presheaf.germ U x hx = X.presheaf.germ (⊤ : X.Opens) x (Opens.mem_top x)`. Simplify using the standard rewrite rules. Establish `key' : (X.presheaf.germ U x hx).hom.comp (X.presheaf.map (homOfLE hle).op).hom = (X.presheaf.germ (⊤ : X.Opens) x (Opens.mem_top x)).hom`. Rewrite using `[← CommRingCat.hom_comp, key]`.

Use `show (X.presheaf.germ U x hx).hom.comp (sectionsAlgebraMap k p U) = (X.presheaf.germ (⊤ : X.Opens) x (Opens.mem_top x)).hom.comp (sectionsAlgebraMap k p ⊤)`. Rewrite using `[← key', RingHom.comp_assoc, sectionsAlgebraMap_comp_restrict k p hle]`.
-/
theorem sectionsAlgebraMap_comp_germ (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (x : X) (hx : x ∈ U) :
    (X.presheaf.germ U x hx).hom.comp (sectionsAlgebraMap k p U) = stalkAlgebraMap k p x := by
  have hle : U ≤ (⊤ : X.Opens) := le_top
  have key : X.presheaf.map (homOfLE hle).op ≫ X.presheaf.germ U x hx
      = X.presheaf.germ (⊤ : X.Opens) x (Opens.mem_top x) := by
    simp
  have key' : (X.presheaf.germ U x hx).hom.comp (X.presheaf.map (homOfLE hle).op).hom
      = (X.presheaf.germ (⊤ : X.Opens) x (Opens.mem_top x)).hom := by
    rw [← CommRingCat.hom_comp, key]
  show (X.presheaf.germ U x hx).hom.comp (sectionsAlgebraMap k p U)
      = (X.presheaf.germ (⊤ : X.Opens) x (Opens.mem_top x)).hom.comp (sectionsAlgebraMap k p ⊤)
  rw [← key', RingHom.comp_assoc, sectionsAlgebraMap_comp_restrict k p hle]

/- English proof (translation)
The claim follows from `DFunLike.congr_fun (sectionsAlgebraMap_comp_germ k p U x hx) a`.
-/
theorem germ_sectionsAlgebraMap_apply (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (x : X) (hx : x ∈ U) (a : k) :
    (X.presheaf.germ U x hx).hom (sectionsAlgebraMap k p U a) = stalkAlgebraMap k p x a :=
  DFunLike.congr_fun (sectionsAlgebraMap_comp_germ k p U x hx) a

/- English proof (translation)
Use `IsScalarTower.of_algebraMap_eq' ?_` and prove the remaining obligations. Rewrite using `[hstalk, hgerm, hU, sectionsAlgebraMap_comp_germ]`.
-/
theorem isScalarTower_stalk (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (x : X) (hx : x ∈ U)
    [Algebra k Γ(X, U)] [Algebra k (X.presheaf.stalk x)] [Algebra Γ(X, U) (X.presheaf.stalk x)]
    (hU : algebraMap k Γ(X, U) = sectionsAlgebraMap k p U)
    (hstalk : algebraMap k (X.presheaf.stalk x) = stalkAlgebraMap k p x)
    (hgerm : algebraMap Γ(X, U) (X.presheaf.stalk x) = (X.presheaf.germ U x hx).hom) :
    IsScalarTower k Γ(X, U) (X.presheaf.stalk x) := by
  refine IsScalarTower.of_algebraMap_eq' ?_
  rw [hstalk, hgerm, hU, sectionsAlgebraMap_comp_germ]

/- English proof (translation)
Break down `isEmpty_or_nonempty {U : X.affineOpens // x ∈ U.1.1} with hE | ⟨⟨U, hx⟩⟩` into its components or cases. Establish `h1 : ∀ J : X.IdealSheafData, stalkIdeal J x = ⊥` using `fun J => iSup_of_empty (fun U : {U : X.affineOpens // x ∈ U.1.1} => Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (J.ideal U.1))`. Rewrite using `[h1 (derivIdealSheaf k p I), h1 I]`. Conclude with `(@derivIdeal_bot k _ _ _ (stalkAlgebra k p x)).symm`. Establish `hU : IsAffineOpen U.1` using `U.2`.

Set `algk : Algebra k Γ(X, U.1)` to `sectionsAlgebra k p U.1`. Set `algst : Algebra k (X.presheaf.stalk x)` to `stalkAlgebra k p x`. Set `algS : Algebra Γ(X, U.1) (X.presheaf.stalk x)` to `(X.presheaf.germ U.1 x hx).hom.toAlgebra`. Establish `: IsScalarTower k Γ(X, U.1) (X.presheaf.stalk x)` using `isScalarTower_stalk k p U.1 x hx rfl rfl rfl`. Establish `: Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1))` using `finitePresentation_kaehlerDifferential_sections k p U rfl`.

Establish `_hloc : IsLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x)` using `hU.isLocalization_stalk ⟨x, hx⟩`. Rewrite using `[stalkIdeal_eq_map_germ (derivIdealSheaf k p I) x U hx, stalkIdeal_eq_map_germ I x U hx, derivIdealSheaf_ideal]`. Conclude with `map_derivIdeal (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (I.ideal U)`.
-/
theorem stalkIdeal_derivIdealSheaf (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (x : X) :
    stalkIdeal (derivIdealSheaf k p I) x =
      @derivIdeal k _ _ _ (stalkAlgebra k p x) (stalkIdeal I x) := by
  rcases isEmpty_or_nonempty {U : X.affineOpens // x ∈ U.1.1} with hE | ⟨⟨U, hx⟩⟩
  · have h1 : ∀ J : X.IdealSheafData, stalkIdeal J x = ⊥ := fun J =>
      iSup_of_empty (fun U : {U : X.affineOpens // x ∈ U.1.1} =>
        Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (J.ideal U.1))
    rw [h1 (derivIdealSheaf k p I), h1 I]
    exact (@derivIdeal_bot k _ _ _ (stalkAlgebra k p x)).symm
  · have hU : IsAffineOpen U.1 := U.2
    let algk : Algebra k Γ(X, U.1) := sectionsAlgebra k p U.1
    let algst : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
    let algS : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
      (X.presheaf.germ U.1 x hx).hom.toAlgebra
    have : IsScalarTower k Γ(X, U.1) (X.presheaf.stalk x) :=
      isScalarTower_stalk k p U.1 x hx rfl rfl rfl
    have : Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) :=
      finitePresentation_kaehlerDifferential_sections k p U rfl
    have _hloc : IsLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
        (X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hx⟩
    rw [stalkIdeal_eq_map_germ (derivIdealSheaf k p I) x U hx,
      stalkIdeal_eq_map_germ I x U hx, derivIdealSheaf_ideal]
    exact map_derivIdeal (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (I.ideal U)

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => rfl`. Consider the case `succ r ih`. Establish `h` using `stalkIdeal_derivIdealSheaf k p (derivIdealSheafIterate k p r I) x`. Rewrite using `[derivIdealSheafIterate_succ, h, ih, derivIdealIterate_succ]`.
-/
theorem stalkIdeal_derivIdealSheafIterate (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (r : ℕ)
    (I : X.IdealSheafData) (x : X) :
    stalkIdeal (derivIdealSheafIterate k p r I) x =
      @derivIdealIterate k _ _ _ (stalkAlgebra k p x) r (stalkIdeal I x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      have h := stalkIdeal_derivIdealSheaf k p (derivIdealSheafIterate k p r I) x
      rw [derivIdealSheafIterate_succ, h, ih, derivIdealIterate_succ]

/- English proof (translation)
Rewrite `h`, the goal using `[le_orderAt_iff]`. Rewrite using `[stalkIdeal_derivIdealSheafIterate k p r I x]`. Establish `key` using `@derivIdealIterate_le_pow_of_le_pow k _ _ _ (stalkAlgebra k p x) (stalkIdeal I x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (n + r) r h`. Rewrite `key` using `[Nat.add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem le_orderAt_derivIdealSheafIterate (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (x : X) (n r : ℕ) (h : ((n + r : ℕ) : ℕ∞) ≤ orderAt I x) :
    (n : ℕ∞) ≤ orderAt (derivIdealSheafIterate k p r I) x := by
  rw [le_orderAt_iff] at h ⊢
  rw [stalkIdeal_derivIdealSheafIterate k p r I x]
  have key := @derivIdealIterate_le_pow_of_le_pow k _ _ _ (stalkAlgebra k p x)
    (stalkIdeal I x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (n + r) r h
  rwa [Nat.add_sub_cancel] at key

/- English proof (translation)
Break down `Nat.lt_or_ge m r with h | h` into its components or cases. Rewrite using `[show m - r = 0 from Nat.sub_eq_zero_of_le (le_of_lt h), orderAtLeastLocus_zero]`. Conclude with `Set.subset_univ _`. Introduce `x hx`. Rewrite `hx`, the goal using `[mem_orderAtLeastLocus_iff]`.

Use `le_orderAt_derivIdealSheafIterate k p I x (m - r) r ?_` and prove the remaining obligations. Rewrite using `[Nat.sub_add_cancel h]`. Conclude with `hx`.
-/
theorem orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate (k : Type u) [CommRing k]
    [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] (I : X.IdealSheafData) (r m : ℕ) :
    orderAtLeastLocus I m ⊆ orderAtLeastLocus (derivIdealSheafIterate k p r I) (m - r) := by
  rcases Nat.lt_or_ge m r with h | h
  · rw [show m - r = 0 from Nat.sub_eq_zero_of_le (le_of_lt h), orderAtLeastLocus_zero]
    exact Set.subset_univ _
  · intro x hx
    rw [mem_orderAtLeastLocus_iff] at hx ⊢
    refine le_orderAt_derivIdealSheafIterate k p I x (m - r) r ?_
    rw [Nat.sub_add_cancel h]
    exact hx

/- English proof (translation)
Establish `: Algebra.FormallySmooth k k` using `inferInstance`. Conclude with `Algebra.FormallySmooth.of_equiv (AlgEquiv.ofRingEquiv (f := e) (fun x => he x))`.
-/
private theorem formallySmooth_of_ringEquiv (k : Type u) [CommRing k] (R : Type u)
    [CommRing R] [Algebra k R] (e : k ≃+* R) (he : ∀ x : k, e x = algebraMap k R x) :
    Algebra.FormallySmooth k R := by
  have : Algebra.FormallySmooth k k := inferInstance
  exact Algebra.FormallySmooth.of_equiv (AlgEquiv.ofRingEquiv (f := e) (fun x => he x))

/- English proof (translation)
Establish `hQ : RingHom.Smooth (p.appLE ⊤ U (le_preimage_top k p U)).hom` using `(AlgebraicGeometry.smooth_iff p).mp ‹AlgebraicGeometry.Smooth p› (isAffineOpen_top (Spec (CommRingCat.of k))) hU (le_preimage_top k p U)`. Set `algSections : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U)` to `(p.appLE ⊤ U (le_preimage_top k p U)).hom.toAlgebra`. Establish `hS : Algebra.Smooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U)` using `hQ`. Establish `: Algebra.FormallySmooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U)` using `hS.formallySmooth`. Set `algGlobal : Algebra k Γ(Spec (CommRingCat.of k), ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toAlgebra`.

Establish `: Algebra.FormallySmooth k Γ(Spec (CommRingCat.of k), ⊤)` using `formallySmooth_of_ringEquiv k Γ(Spec (CommRingCat.of k), ⊤) (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv (fun _ => rfl)`. Establish `: IsScalarTower k Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U)` using `IsScalarTower.of_algebraMap_eq' (h.trans rfl)`. Conclude with `Algebra.FormallySmooth.comp k Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U)`.
-/
theorem formallySmooth_sections (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (U : X.Opens)
    (hU : IsAffineOpen U) [Algebra k Γ(X, U)]
    (h : algebraMap k Γ(X, U) = sectionsAlgebraMap k p U) :
    Algebra.FormallySmooth k Γ(X, U) := by
  have hQ : RingHom.Smooth (p.appLE ⊤ U (le_preimage_top k p U)).hom :=
    (AlgebraicGeometry.smooth_iff p).mp ‹AlgebraicGeometry.Smooth p›
      (isAffineOpen_top (Spec (CommRingCat.of k))) hU (le_preimage_top k p U)
  let algSections : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) :=
    (p.appLE ⊤ U (le_preimage_top k p U)).hom.toAlgebra
  have hS : Algebra.Smooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) := hQ
  have : Algebra.FormallySmooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) := hS.formallySmooth
  let algGlobal : Algebra k Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toAlgebra
  have : Algebra.FormallySmooth k Γ(Spec (CommRingCat.of k), ⊤) :=
    formallySmooth_of_ringEquiv k Γ(Spec (CommRingCat.of k), ⊤)
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv (fun _ => rfl)
  have : IsScalarTower k Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq' (h.trans rfl)
  exact Algebra.FormallySmooth.comp k Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U)

/- English proof (translation)
Establish `: IsNoetherianRing k` using `inferInstance`. Establish `hQ : RingHom.Smooth (p.appLE ⊤ U (le_preimage_top k p U)).hom` using `(AlgebraicGeometry.smooth_iff p).mp ‹AlgebraicGeometry.Smooth p› (isAffineOpen_top (Spec (CommRingCat.of k))) hU (le_preimage_top k p U)`. Set `algSections : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U)` to `(p.appLE ⊤ U (le_preimage_top k p U)).hom.toAlgebra`. Establish `hS : Algebra.Smooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U)` using `hQ`. Establish `e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤)` using `(Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv`.

Establish `: IsNoetherianRing Γ(Spec (CommRingCat.of k), ⊤)` using `isNoetherianRing_of_surjective k (↥Γ(Spec (CommRingCat.of k), ⊤)) e.toRingHom e.surjective`. Take `⟨n, f, hf, -⟩` from `hS.finitePresentation`. Conclude with `isNoetherianRing_of_surjective (MvPolynomial (Fin n) (↥Γ(Spec (CommRingCat.of k), ⊤))) (↥Γ(X, U)) f.toRingHom hf`.
-/
private theorem isNoetherianRing_sections_of_smooth (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (U : X.Opens)
    (hU : IsAffineOpen U) : IsNoetherianRing Γ(X, U) := by
  have : IsNoetherianRing k := inferInstance
  have hQ : RingHom.Smooth (p.appLE ⊤ U (le_preimage_top k p U)).hom :=
    (AlgebraicGeometry.smooth_iff p).mp ‹AlgebraicGeometry.Smooth p›
      (isAffineOpen_top (Spec (CommRingCat.of k))) hU (le_preimage_top k p U)
  let algSections : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) :=
    (p.appLE ⊤ U (le_preimage_top k p U)).hom.toAlgebra
  have hS : Algebra.Smooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) := hQ
  have e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ(Spec (CommRingCat.of k), ⊤) :=
    isNoetherianRing_of_surjective k (↥Γ(Spec (CommRingCat.of k), ⊤)) e.toRingHom e.surjective
  obtain ⟨n, f, hf, -⟩ := hS.finitePresentation
  exact isNoetherianRing_of_surjective
    (MvPolynomial (Fin n) (↥Γ(Spec (CommRingCat.of k), ⊤))) (↥Γ(X, U)) f.toRingHom hf

/- English proof (translation)
Establish `: IsLocallyNoetherian X` using `⟨fun U => isNoetherianRing_sections_of_smooth k p U.1 U.2⟩`. Use `infer_instance`.
-/
theorem isNoetherianRing_stalk (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    IsNoetherianRing (X.presheaf.stalk x) := by
  have : IsLocallyNoetherian X := ⟨fun U => isNoetherianRing_sections_of_smooth k p U.1 U.2⟩
  infer_instance

/- English proof (translation)
Assemble the required witnesses or components as `⟨(X.affineCover.f (X.affineCover.idx x)).opensRange, X.affineCover.covers x, isAffineOpen_opensRange _⟩`.
-/
private theorem exists_isAffineOpen_mem (X : Scheme.{u}) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U :=
  ⟨(X.affineCover.f (X.affineCover.idx x)).opensRange, X.affineCover.covers x,
    isAffineOpen_opensRange _⟩

/- English proof (translation)
Take `⟨U, hxU, hU⟩` from `exists_isAffineOpen_mem X x`. Set `algU : Algebra k Γ(X, U)` to `sectionsAlgebra k p U`. Set `algStalk : Algebra k (X.presheaf.stalk x)` to `stalkAlgebra k p x`. Set `algGerm : Algebra Γ(X, U) (X.presheaf.stalk x)` to `(X.presheaf.germ U x hxU).hom.toAlgebra`. Establish `_tower : IsScalarTower k Γ(X, U) (X.presheaf.stalk x)` using `isScalarTower_stalk k p U x hxU rfl rfl rfl`.

Establish `_fsU : Algebra.FormallySmooth k Γ(X, U)` using `formallySmooth_sections k p U hU rfl`. Establish `_loc : IsLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (X.presheaf.stalk x)` using `hU.isLocalization_stalk ⟨x, hxU⟩`. Establish `_fsStalk : Algebra.FormallySmooth Γ(X, U) (X.presheaf.stalk x)` using `Algebra.FormallySmooth.of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl`. Conclude with `Algebra.FormallySmooth.comp k Γ(X, U) (X.presheaf.stalk x)`.
-/
theorem formallySmooth_stalk (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    @Algebra.FormallySmooth k _ _ _ (stalkAlgebra k p x) := by
  obtain ⟨U, hxU, hU⟩ := exists_isAffineOpen_mem X x
  let algU : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let algStalk : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
  let algGerm : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have _tower : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) :=
    isScalarTower_stalk k p U x hxU rfl rfl rfl
  have _fsU : Algebra.FormallySmooth k Γ(X, U) := formallySmooth_sections k p U hU rfl
  have _loc : IsLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hxU⟩
  have _fsStalk : Algebra.FormallySmooth Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.FormallySmooth.of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  exact Algebra.FormallySmooth.comp k Γ(X, U) (X.presheaf.stalk x)

/- English proof (translation)
Use `hfin` as an intermediate fact. Establish `: IsLocalizedModule M (KaehlerDifferential.map k k A B)` using `inferInstance`. Establish `hbc : IsBaseChange B (KaehlerDifferential.map k k A B)` using `IsLocalizedModule.isBaseChange M B (KaehlerDifferential.map k k A B)`. Establish `: Module.Finite B (TensorProduct A B (KaehlerDifferential k A))` using `inferInstance`. Conclude with `Module.Finite.equiv hbc.equiv`.
-/
private theorem finite_kaehlerDifferential_of_isLocalization (k A B : Type u) [CommRing k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (M : Submonoid A) [IsLocalization M B]
    (hfin : Module.Finite A (KaehlerDifferential k A)) :
    Module.Finite B (KaehlerDifferential k B) := by
  have := hfin
  have : IsLocalizedModule M (KaehlerDifferential.map k k A B) := inferInstance
  have hbc : IsBaseChange B (KaehlerDifferential.map k k A B) :=
    IsLocalizedModule.isBaseChange M B (KaehlerDifferential.map k k A B)
  have : Module.Finite B (TensorProduct A B (KaehlerDifferential k A)) := inferInstance
  exact Module.Finite.equiv hbc.equiv

/- English proof (translation)
Set `algStalk : Algebra k (X.presheaf.stalk x)` to `stalkAlgebra k p x`. Use `show Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x))`. Take `⟨U, hxU, hUaff⟩` from `exists_isAffineOpen_mem X x`. Set `algSections : Algebra k Γ(X, U)` to `sectionsAlgebra k p U`. Set `algGerm : Algebra Γ(X, U) (X.presheaf.stalk x)` to `(X.presheaf.germ U x hxU).hom.toAlgebra`.

Establish `: IsScalarTower k Γ(X, U) (X.presheaf.stalk x)` using `isScalarTower_stalk k p U x hxU rfl rfl rfl`. Establish `: IsLocalization (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (X.presheaf.stalk x)` using `hUaff.isLocalization_stalk ⟨x, hxU⟩`. Establish `: Module.FinitePresentation Γ(X, U) (KaehlerDifferential k Γ(X, U))` using `finitePresentation_kaehlerDifferential_sections k p ⟨U, hUaff⟩ rfl`. Conclude with `finite_kaehlerDifferential_of_isLocalization k Γ(X, U) (X.presheaf.stalk x) (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl inferInstance`.
-/
theorem finite_kaehlerDifferential_stalk (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    letI := stalkAlgebra k p x
    Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) := by
  let algStalk : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
  show Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x))
  obtain ⟨U, hxU, hUaff⟩ := exists_isAffineOpen_mem X x
  let algSections : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let algGerm : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) :=
    isScalarTower_stalk k p U x hxU rfl rfl rfl
  have : IsLocalization (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := hUaff.isLocalization_stalk ⟨x, hxU⟩
  have : Module.FinitePresentation Γ(X, U) (KaehlerDifferential k Γ(X, U)) :=
    finitePresentation_kaehlerDifferential_sections k p ⟨U, hUaff⟩ rfl
  exact finite_kaehlerDifferential_of_isLocalization k Γ(X, U) (X.presheaf.stalk x)
    (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl inferInstance

/- English proof (translation)
Establish `_h1 : Module.FinitePresentation A (KaehlerDifferential k A)` using `Module.finitePresentation_of_finite ..`. Establish `_h2 : Module.Projective A (KaehlerDifferential k A)` using `inferInstance`. Establish `_h3 : Module.Flat A (KaehlerDifferential k A)` using `inferInstance`. Conclude with `Module.free_of_flat_of_isLocalRing`.
-/
private theorem free_kaehlerDifferential_of_formallySmooth (k : Type u) [Field k] (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FormallySmooth k A]
    [Module.Finite A (KaehlerDifferential k A)] :
    Module.Free A (KaehlerDifferential k A) := by
  have _h1 : Module.FinitePresentation A (KaehlerDifferential k A) :=
    Module.finitePresentation_of_finite ..
  have _h2 : Module.Projective A (KaehlerDifferential k A) := inferInstance
  have _h3 : Module.Flat A (KaehlerDifferential k A) := inferInstance
  exact Module.free_of_flat_of_isLocalRing

/- English proof (translation)
Set `algst : Algebra k (X.presheaf.stalk x)` to `stalkAlgebra k p x`. Establish `_hN : IsNoetherianRing (X.presheaf.stalk x)` using `isNoetherianRing_stalk k p x`. Establish `_hFS : Algebra.FormallySmooth k (X.presheaf.stalk x)` using `formallySmooth_stalk k p x`. Establish `_hFin : Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x))` using `finite_kaehlerDifferential_stalk k p x`. Conclude with `free_kaehlerDifferential_of_formallySmooth k (X.presheaf.stalk x)`.
-/
theorem free_kaehlerDifferential_stalk (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    letI := stalkAlgebra k p x
    Module.Free (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) := by
  let algst : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
  have _hN : IsNoetherianRing (X.presheaf.stalk x) := isNoetherianRing_stalk k p x
  have _hFS : Algebra.FormallySmooth k (X.presheaf.stalk x) := formallySmooth_stalk k p x
  have _hFin : Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) :=
    finite_kaehlerDifferential_stalk k p x
  exact free_kaehlerDifferential_of_formallySmooth k (X.presheaf.stalk x)

/- English proof (translation)
Establish `hne : ((n : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Establish `hk : IsUnit ((n : ℕ) : k)` using `IsUnit.mk0 _ hne`. Establish `h` using `hk.map (stalkAlgebraMap k p x)`. Rewrite `h` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem isUnit_natCast_stalk (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) {n : ℕ} (hn : 1 ≤ n) :
    IsUnit ((n : ℕ) : X.presheaf.stalk x) := by
  have hne : ((n : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk : IsUnit ((n : ℕ) : k) := IsUnit.mk0 _ hne
  have h := hk.map (stalkAlgebraMap k p x)
  rwa [map_natCast] at h

/- English proof (translation)
Establish `hunit : ∀ y : nonZeroDivisors A₀, IsUnit (algebraMap A₀ L y)`. Introduce `y`. Use `isUnit_iff_ne_zero.mpr (fun hy => ?_)` and prove the remaining obligations. Establish `h0 : (y : A₀) = 0` using `hinj (by rw [hy, map_zero])`. Conclude with `nonZeroDivisors.coe_ne_zero y h0`.

Set `algFL : Algebra (FractionRing A₀) L` to `(IsLocalization.lift hunit).toAlgebra`. Establish `_twr1 : IsScalarTower k A₀ (FractionRing A₀)` using `inferInstance`. Establish `_twr2 : IsScalarTower A₀ (FractionRing A₀) L` using `IsScalarTower.of_algebraMap_eq (fun a => (IsLocalization.lift_eq hunit a).symm)`. Establish `_twr3 : IsScalarTower k (FractionRing A₀) L`. Use `IsScalarTower.of_algebraMap_eq (fun c => ?_)` and prove the remaining obligations.

Rewrite using `[IsScalarTower.algebraMap_apply k A₀ (FractionRing A₀) c, ← IsScalarTower.algebraMap_apply A₀ (FractionRing A₀) L, ← IsScalarTower.algebraMap_apply k A₀ L]`. Establish `_fs1 : Algebra.FormallySmooth A₀ (FractionRing A₀)` using `Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors A₀)`. Establish `_fs2 : Algebra.FormallySmooth k (FractionRing A₀)` using `Algebra.FormallySmooth.comp k A₀ (FractionRing A₀)`. Establish `_hchar : CharZero (FractionRing A₀)` using `charZero_of_injective_algebraMap (RingHom.injective (algebraMap k (FractionRing A₀)))`. Establish `_halgF : Algebra.IsAlgebraic (FractionRing A₀) L`.

Use `⟨fun a => ?_⟩` and prove the remaining obligations. Take `⟨q, hq0, hqa⟩` from `(Algebra.IsAlgebraic.isAlgebraic a : IsAlgebraic A₀ a)`. Use `⟨q.map (algebraMap A₀ (FractionRing A₀)), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Polynomial.map_ne_zero_iff (IsFractionRing.injective A₀ (FractionRing A₀))).mpr hq0`. Rewrite using `[Polynomial.aeval_map_algebraMap]`.

Conclude with `hqa`. Establish `_hsep : Algebra.IsSeparable (FractionRing A₀) L`. Use `⟨fun a => ?_⟩` and prove the remaining obligations. Conclude with `(minpoly.irreducible ((Algebra.IsAlgebraic.isAlgebraic a : IsAlgebraic (FractionRing A₀) a).isIntegral)).separable`. Establish `_fet : Algebra.FormallyEtale (FractionRing A₀) L` using `Algebra.FormallyEtale.of_isSeparable ..`.

Establish `_fs3 : Algebra.FormallySmooth (FractionRing A₀) L` using `inferInstance`. Conclude with `Algebra.FormallySmooth.comp k (FractionRing A₀) L`.
-/
private theorem formallySmooth_of_isAlgebraic (k : Type u) [Field k] [CharZero k] (L : Type u)
    [Field L] [Algebra k L] (A₀ : Type u) [CommRing A₀] [IsDomain A₀] [Algebra k A₀] [Algebra A₀ L]
    [IsScalarTower k A₀ L] [Algebra.FormallySmooth k A₀] [Algebra.IsAlgebraic A₀ L]
    (hinj : Function.Injective (algebraMap A₀ L)) :
    Algebra.FormallySmooth k L := by
  have hunit : ∀ y : nonZeroDivisors A₀, IsUnit (algebraMap A₀ L y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr (fun hy => ?_)
    have h0 : (y : A₀) = 0 := hinj (by rw [hy, map_zero])
    exact nonZeroDivisors.coe_ne_zero y h0
  let algFL : Algebra (FractionRing A₀) L := (IsLocalization.lift hunit).toAlgebra
  have _twr1 : IsScalarTower k A₀ (FractionRing A₀) := inferInstance
  have _twr2 : IsScalarTower A₀ (FractionRing A₀) L :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsLocalization.lift_eq hunit a).symm)
  have _twr3 : IsScalarTower k (FractionRing A₀) L := by
    refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    rw [IsScalarTower.algebraMap_apply k A₀ (FractionRing A₀) c,
      ← IsScalarTower.algebraMap_apply A₀ (FractionRing A₀) L,
      ← IsScalarTower.algebraMap_apply k A₀ L]
  have _fs1 : Algebra.FormallySmooth A₀ (FractionRing A₀) :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors A₀)
  have _fs2 : Algebra.FormallySmooth k (FractionRing A₀) :=
    Algebra.FormallySmooth.comp k A₀ (FractionRing A₀)
  have _hchar : CharZero (FractionRing A₀) :=
    charZero_of_injective_algebraMap (RingHom.injective (algebraMap k (FractionRing A₀)))
  have _halgF : Algebra.IsAlgebraic (FractionRing A₀) L := by
    refine ⟨fun a => ?_⟩
    obtain ⟨q, hq0, hqa⟩ := (Algebra.IsAlgebraic.isAlgebraic a : IsAlgebraic A₀ a)
    refine ⟨q.map (algebraMap A₀ (FractionRing A₀)), ?_, ?_⟩
    · exact (Polynomial.map_ne_zero_iff
        (IsFractionRing.injective A₀ (FractionRing A₀))).mpr hq0
    · rw [Polynomial.aeval_map_algebraMap]
      exact hqa
  have _hsep : Algebra.IsSeparable (FractionRing A₀) L := by
    refine ⟨fun a => ?_⟩
    exact (minpoly.irreducible
      ((Algebra.IsAlgebraic.isAlgebraic a : IsAlgebraic (FractionRing A₀) a).isIntegral)).separable
  have _fet : Algebra.FormallyEtale (FractionRing A₀) L :=
    Algebra.FormallyEtale.of_isSeparable ..
  have _fs3 : Algebra.FormallySmooth (FractionRing A₀) L := inferInstance
  exact Algebra.FormallySmooth.comp k (FractionRing A₀) L

/- English proof (translation)
Establish `hai : AlgebraicIndependent k x` using `hx.1`. Establish `_fsA : Algebra.FormallySmooth k ↥(Algebra.adjoin k (Set.range x))` using `Algebra.FormallySmooth.of_equiv hai.aevalEquiv`. Establish `_halg : Algebra.IsAlgebraic ↥(Algebra.adjoin k (Set.range x)) L` using `hx.isAlgebraic`. Establish `_hdom : IsDomain ↥(Algebra.adjoin k (Set.range x))` using `inferInstance`. Conclude with `formallySmooth_of_isAlgebraic k L ↥(Algebra.adjoin k (Set.range x)) (fun a b h => Subtype.ext h)`.
-/
private theorem formallySmooth_of_isTranscendenceBasis (k : Type u) [Field k] [CharZero k]
    (L : Type u) [Field L] [Algebra k L] {ι : Type u} {x : ι → L}
    (hx : IsTranscendenceBasis k x) : Algebra.FormallySmooth k L := by
  have hai : AlgebraicIndependent k x := hx.1
  have _fsA : Algebra.FormallySmooth k ↥(Algebra.adjoin k (Set.range x)) :=
    Algebra.FormallySmooth.of_equiv hai.aevalEquiv
  have _halg : Algebra.IsAlgebraic ↥(Algebra.adjoin k (Set.range x)) L := hx.isAlgebraic
  have _hdom : IsDomain ↥(Algebra.adjoin k (Set.range x)) := inferInstance
  exact formallySmooth_of_isAlgebraic k L ↥(Algebra.adjoin k (Set.range x))
    (fun a b h => Subtype.ext h)

/- English proof (translation)
Take `⟨B, hB⟩` from `exists_isTranscendenceBasis k L`. Conclude with `formallySmooth_of_isTranscendenceBasis k L hB`.
-/
private theorem formallySmooth_of_charZero (k : Type u) [Field k] [CharZero k] (L : Type u) [Field L]
    [Algebra k L] : Algebra.FormallySmooth k L := by
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis k L
  exact formallySmooth_of_isTranscendenceBasis k L hB

/- English proof (translation)
The claim follows from `formallySmooth_of_charZero k (IsLocalRing.ResidueField (X.presheaf.stalk x))`.
-/
theorem formallySmooth_residueField (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X)
    [Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk x))]
    (_h : algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x)) =
      (IsLocalRing.residue (X.presheaf.stalk x)).comp (stalkAlgebraMap k p x)) :
    Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
  formallySmooth_of_charZero k (IsLocalRing.ResidueField (X.presheaf.stalk x))

/- English proof (translation)
Set `algst : Algebra k (X.presheaf.stalk x)` to `stalkAlgebra k p x`. Establish `_hN : IsNoetherianRing (X.presheaf.stalk x)` using `isNoetherianRing_stalk k p x`. Establish `_hFS : Algebra.FormallySmooth k (X.presheaf.stalk x)` using `formallySmooth_stalk k p x`. Establish `_hFin : Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x))` using `finite_kaehlerDifferential_stalk k p x`. Establish `_hFree : Module.Free (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x))` using `free_kaehlerDifferential_stalk k p x`.

Set `algres : Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk x))` to `((IsLocalRing.residue (X.presheaf.stalk x)).comp (stalkAlgebraMap k p x)).toAlgebra`. Establish `_tower : IsScalarTower k (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x))` using `IsScalarTower.of_algebraMap_eq' rfl`. Establish `_hFSres : Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x))` using `formallySmooth_residueField k p x rfl`. Take `⟨h, y, δ, hspan, hδ⟩` from `exists_local_parameters_and_dual_derivations k (X.presheaf.stalk x)`. Establish `hI' : idealOrder (stalkIdeal I x) = (r : ℕ∞)`.

Rewrite using `[← orderAt_eq_idealOrder]`. Conclude with `hr`. Rewrite using `[orderAt_eq_idealOrder, stalkIdeal_derivIdealSheafIterate k p j I x]`. Conclude with `idealOrder_derivIdealIterate_of_isUnit_natCast k y δ hδ hspan (fun n hn => isUnit_natCast_stalk k p x hn) hI' hj`.
-/
theorem orderAt_derivIdealSheafIterate_eq_sub (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (I : X.IdealSheafData)
    (x : X) {r : ℕ} (hr : orderAt I x = (r : ℕ∞)) {j : ℕ} (hj : j ≤ r) :
    orderAt (derivIdealSheafIterate k p j I) x = ((r - j : ℕ) : ℕ∞) := by
  let algst : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
  have _hN : IsNoetherianRing (X.presheaf.stalk x) := isNoetherianRing_stalk k p x
  have _hFS : Algebra.FormallySmooth k (X.presheaf.stalk x) := formallySmooth_stalk k p x
  have _hFin : Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) :=
    finite_kaehlerDifferential_stalk k p x
  have _hFree : Module.Free (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) :=
    free_kaehlerDifferential_stalk k p x
  let algres : Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    ((IsLocalRing.residue (X.presheaf.stalk x)).comp (stalkAlgebraMap k p x)).toAlgebra
  have _tower : IsScalarTower k (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have _hFSres : Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    formallySmooth_residueField k p x rfl
  obtain ⟨h, y, δ, hspan, hδ⟩ := exists_local_parameters_and_dual_derivations k (X.presheaf.stalk x)
  have hI' : idealOrder (stalkIdeal I x) = (r : ℕ∞) := by
    rw [← orderAt_eq_idealOrder]; exact hr
  rw [orderAt_eq_idealOrder, stalkIdeal_derivIdealSheafIterate k p j I x]
  exact idealOrder_derivIdealIterate_of_isUnit_natCast k y δ hδ hspan
    (fun n hn => isUnit_natCast_stalk k p x hn) hI' hj

/- English proof (translation)
Break down `eq_or_ne a ⊤ with h | h` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr ⟨a.toNat, (ENat.natCast_toNat h).symm⟩`.
-/
private theorem eq_top_or_exists_eq_natCast (a : ℕ∞) : a = ⊤ ∨ ∃ n : ℕ, a = (n : ℕ∞) := by
  rcases eq_or_ne a ⊤ with h | h
  · exact Or.inl h
  · exact Or.inr ⟨a.toNat, (ENat.natCast_toNat h).symm⟩

/- English proof (translation)
Use `Set.Subset.antisymm ?_ (orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate k p I r m)` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx`, the goal using `[mem_orderAtLeastLocus_iff]`. Break down `eq_top_or_exists_eq_natCast (orderAt I x) with htop | ⟨n, hn⟩` into its components or cases. Rewrite using `[htop]`.

Conclude with `le_top`. Break down `Nat.lt_or_ge n r with hnr | hrn` into its components or cases. It suffices to derive a contradiction. Establish `hzero : orderAt (derivIdealSheafIterate k p n I) x = ((n - n : ℕ) : ℕ∞)` using `orderAt_derivIdealSheafIterate_eq_sub k p I x hn le_rfl`. Simplify using `only [Nat.sub_self, Nat.cast_zero] at hzero`.

Establish `hsplit : r - n + n = r` using `by omega`. Establish `hadd : derivIdealSheafIterate k p (r - n + n) I = derivIdealSheafIterate k p (r - n) (derivIdealSheafIterate k p n I)` using `derivIdealSheafIterate_add k p (r - n) n I`. Rewrite `hadd` using `[hsplit]`. Establish `hle : derivIdealSheafIterate k p n I ≤ derivIdealSheafIterate k p r I`. Rewrite using `[hadd]`.

Conclude with `le_derivIdealSheafIterate k p (r - n) (derivIdealSheafIterate k p n I)`. Establish `h1 : orderAt (derivIdealSheafIterate k p r I) x ≤ 0`. Establish `h2` using `orderAt_le_of_le hle x`. Rewrite `h2` using `[hzero]`. Then use the resulting hypothesis. Establish `h3 : ((m - r : ℕ) : ℕ∞) ≤ 0` using `le_trans hx h1`.

Establish `h4 : m - r ≤ 0` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers. Establish `key : orderAt (derivIdealSheafIterate k p r I) x = ((n - r : ℕ) : ℕ∞)` using `orderAt_derivIdealSheafIterate_eq_sub k p I x hn hrn`. Rewrite `hx` using `[key]`. Establish `hmn : m - r ≤ n - r` using `by exact_mod_cast hx`.

Establish `hmn' : m ≤ n` using `by omega`. Rewrite using `[hn]`. Conclude with `hmn'` after adjusting the coercions.
-/
theorem orderAtLeastLocus_derivIdealSheafIterate (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (I : X.IdealSheafData)
    {r m : ℕ} (h : r < m) :
    orderAtLeastLocus (derivIdealSheafIterate k p r I) (m - r) = orderAtLeastLocus I m := by
  refine Set.Subset.antisymm ?_ (orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate k p I r m)
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  rcases eq_top_or_exists_eq_natCast (orderAt I x) with htop | ⟨n, hn⟩
  · rw [htop]
    exact le_top
  · rcases Nat.lt_or_ge n r with hnr | hrn
    · exfalso
      have hzero : orderAt (derivIdealSheafIterate k p n I) x = ((n - n : ℕ) : ℕ∞) :=
        orderAt_derivIdealSheafIterate_eq_sub k p I x hn le_rfl
      simp only [Nat.sub_self, Nat.cast_zero] at hzero
      have hsplit : r - n + n = r := by omega
      have hadd : derivIdealSheafIterate k p (r - n + n) I =
          derivIdealSheafIterate k p (r - n) (derivIdealSheafIterate k p n I) :=
        derivIdealSheafIterate_add k p (r - n) n I
      rw [hsplit] at hadd
      have hle : derivIdealSheafIterate k p n I ≤ derivIdealSheafIterate k p r I := by
        rw [hadd]
        exact le_derivIdealSheafIterate k p (r - n) (derivIdealSheafIterate k p n I)
      have h1 : orderAt (derivIdealSheafIterate k p r I) x ≤ 0 := by
        have h2 := orderAt_le_of_le hle x
        rwa [hzero] at h2
      have h3 : ((m - r : ℕ) : ℕ∞) ≤ 0 := le_trans hx h1
      have h4 : m - r ≤ 0 := by exact_mod_cast h3
      omega
    · have key : orderAt (derivIdealSheafIterate k p r I) x = ((n - r : ℕ) : ℕ∞) :=
        orderAt_derivIdealSheafIterate_eq_sub k p I x hn hrn
      rw [key] at hx
      have hmn : m - r ≤ n - r := by exact_mod_cast hx
      have hmn' : m ≤ n := by omega
      rw [hn]
      exact_mod_cast hmn'

/- English proof (translation)
Establish `h1 : m - 1 < m` using `by omega`. Establish `h2 : m - (m - 1) = 1` using `by omega`. Establish `h3` using `orderAtLeastLocus_derivIdealSheafIterate k p I (r := m - 1) (m := m) h1`. Rewrite `h3` using `[h2]`. Rewrite using `[← h3]`.

Use extensionality with `x`. Conclude with `(mem_orderAtLeastLocus_one_iff (derivIdealSheafIterate k p (m - 1) I) x).symm`.
-/
theorem support_derivIdealSheafIterate_eq_orderAtLeastLocus (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m) :
    ((derivIdealSheafIterate k p (m - 1) I).support : Set X) = orderAtLeastLocus I m := by
  have h1 : m - 1 < m := by omega
  have h2 : m - (m - 1) = 1 := by omega
  have h3 := orderAtLeastLocus_derivIdealSheafIterate k p I (r := m - 1) (m := m) h1
  rw [h2] at h3
  rw [← h3]
  ext x
  exact (mem_orderAtLeastLocus_one_iff (derivIdealSheafIterate k p (m - 1) I) x).symm

/- English proof (translation)
Break down `Nat.eq_zero_or_pos m with hm | hm` into its components or cases. Substitute `hm` using the available equality. Rewrite using `[orderAtLeastLocus_zero]`. Conclude with `isClosed_univ`. Establish `hm1 : 1 ≤ m` using `by omega`.

Rewrite using `[← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm1]`. Conclude with `(derivIdealSheafIterate k p (m - 1) I).support.2`.
-/
theorem isClosed_orderAtLeastLocus (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (I : X.IdealSheafData)
    (m : ℕ) : IsClosed (orderAtLeastLocus I m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [orderAtLeastLocus_zero]
    exact isClosed_univ
  · have hm1 : 1 ≤ m := by omega
    rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm1]
    exact (derivIdealSheafIterate k p (m - 1) I).support.2

/- English proof (translation)
Establish `hcover : (⨆ f : (J.ideal U : Set Γ(X, U.1)), X.basicOpen (f : Γ(X, U.1))) = U.1`. Use `le_antisymm (iSup_le fun f => X.basicOpen_le (f : Γ(X, U.1))) ?_` and prove the remaining obligations. Rewrite using `[SetLike.le_def]`. Introduce `x hxU`. Establish `hxs : x ∉ J.support`.

Introduce `hc`. Establish `hmem : x ∈ (J.support : Set X)` using `hc`. Rewrite `hmem` using `[hJ]`. Simplify using `at hmem`. Establish `hnle : ¬ stalkIdeal J x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x)` using `fun hc => hxs ((mem_support_iff_stalkIdeal_le_maximalIdeal J x).mpr hc)`.

Rewrite `hnle` using `[stalkIdeal_eq_map_germ J x U hxU, Ideal.map_le_iff_le_comap, SetLike.not_le_iff_exists]`. Take `⟨a, ha, ha2⟩` from `hnle`. Establish `hbo : x ∈ X.basicOpen a`. Use `(X.mem_basicOpen a x hxU).mpr ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Conclude with `ha2 (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hc)))`. Conclude with `Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hbo⟩`. Establish `hspan` using `(IsAffineOpen.iSup_basicOpen_eq_self_iff U.2).mp hcover`. Rewrite `hspan` using `[Ideal.span_eq]`. Then use the resulting hypothesis.
-/
private theorem ideal_eq_top_of_support_eq_empty {X : Scheme.{u}} (J : X.IdealSheafData)
    (hJ : (J.support : Set X) = (∅ : Set X)) (U : X.affineOpens) :
    J.ideal U = ⊤ := by
  have hcover : (⨆ f : (J.ideal U : Set Γ(X, U.1)), X.basicOpen (f : Γ(X, U.1))) = U.1 := by
    refine le_antisymm (iSup_le fun f => X.basicOpen_le (f : Γ(X, U.1))) ?_
    rw [SetLike.le_def]
    intro x hxU
    have hxs : x ∉ J.support := by
      intro hc
      have hmem : x ∈ (J.support : Set X) := hc
      rw [hJ] at hmem
      simp at hmem
    have hnle : ¬ stalkIdeal J x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := fun hc =>
      hxs ((mem_support_iff_stalkIdeal_le_maximalIdeal J x).mpr hc)
    rw [stalkIdeal_eq_map_germ J x U hxU, Ideal.map_le_iff_le_comap,
      SetLike.not_le_iff_exists] at hnle
    obtain ⟨a, ha, ha2⟩ := hnle
    have hbo : x ∈ X.basicOpen a := by
      refine (X.mem_basicOpen a x hxU).mpr ?_
      by_contra hc
      exact ha2 (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr
        (mem_nonunits_iff.mpr hc)))
    exact Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hbo⟩
  have hspan := (IsAffineOpen.iSup_basicOpen_eq_self_iff U.2).mp hcover
  rwa [Ideal.span_eq] at hspan

/- English proof (translation)
Establish `hsupp : ((derivIdealSheafIterate k p m I).support : Set X) = (∅ : Set X)`. Establish `h2` using `support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I (m := m + 1) (Nat.le_add_left 1 m)`. Simplify using `only [Nat.add_sub_cancel] at h2`. Conclude with `h2.trans h`. Use `le_antisymm le_top ?_` and prove the remaining obligations.

Introduce `U`. Rewrite using `[ideal_eq_top_of_support_eq_empty (derivIdealSheafIterate k p m I) hsupp U]`. Conclude with `le_top`.
-/
theorem derivIdealSheafIterate_eq_top_of_orderAtLeastLocus_eq_empty (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (I : X.IdealSheafData)
    (m : ℕ) (h : orderAtLeastLocus I (m + 1) = (∅ : Set X)) :
    derivIdealSheafIterate k p m I = ⊤ := by
  have hsupp : ((derivIdealSheafIterate k p m I).support : Set X) = (∅ : Set X) := by
    have h2 := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I (m := m + 1) (Nat.le_add_left 1 m)
    simp only [Nat.add_sub_cancel] at h2
    exact h2.trans h
  refine le_antisymm le_top ?_
  intro U
  rw [ideal_eq_top_of_support_eq_empty (derivIdealSheafIterate k p m I) hsupp U]
  exact le_top

end FunctorialResolution.EmbeddedResolution
