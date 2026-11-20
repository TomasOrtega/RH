import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

universe u

/- English proof (translation)
Establish `: ∀ x : ↥X, _root_.IsReduced ↥(X.presheaf.stalk x)`. Introduce `x`. Take `⟨j, y, hy⟩` from `hcov x`. Use `hm j` as an intermediate fact. Use `hV j` as an intermediate fact.

Substitute `hy` using the available equality. Conclude with `isReduced_of_injective (CommRingCat.Hom.hom ((m j).stalkMap y)) (asIso ((m j).stalkMap y)).commRingCatIsoToRingEquiv.injective`. Conclude with `isReduced_of_isReduced_stalk X`.
-/
private theorem isReduced_of_isOpenImmersion_cover {X : Scheme.{u}} {J : Type u} {V : J → Scheme.{u}}
    (m : (j : J) → V j ⟶ X) (hm : ∀ j, IsOpenImmersion (m j))
    (hV : ∀ j, AlgebraicGeometry.IsReduced (V j))
    (hcov : ∀ x : ↥X, ∃ (j : J) (y : ↥(V j)), (m j).base y = x) :
    AlgebraicGeometry.IsReduced X := by
  have : ∀ x : ↥X, _root_.IsReduced ↥(X.presheaf.stalk x) := by
    intro x
    obtain ⟨j, y, hy⟩ := hcov x
    have := hm j
    have := hV j
    subst hy
    exact isReduced_of_injective (CommRingCat.Hom.hom ((m j).stalkMap y))
      (asIso ((m j).stalkMap y)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk X

/- English proof (translation)
Use `⟨((sigmaMk f).symm x).1, ((sigmaMk f).symm x).2, ?_⟩` and prove the remaining obligations. Rewrite using `[← sigmaMk_mk]`. Simplify using the standard rewrite rules.
-/
private theorem exists_sigma_ι_base_eq {J : Type u} (f : J → Scheme.{u}) (x : ↥(∐ f)) :
    ∃ (j : J) (y : ↥(f j)), (Sigma.ι f j).base y = x := by
  refine ⟨((sigmaMk f).symm x).1, ((sigmaMk f).symm x).2, ?_⟩
  rw [← sigmaMk_mk]
  simp

/- English proof (translation)
Establish `: Subsingleton ↥(Spec (CommRingCat.of k))` using `inferInstance`. Use `⟨fun W hW hW' => ?_⟩` and prove the remaining obligations. Break down `Set.eq_empty_or_nonempty W with rfl | ⟨z, hz⟩` into its components or cases. Simplify using the standard rewrite rules. Establish `hW2 : W = Set.univ` using `Set.eq_univ_of_forall fun w => by`.

Rewrite using `[Subsingleton.elim w z]`. Conclude with `hz`. Rewrite using `[hW2]`. Simplify using `using isCompact_univ`.
-/
private theorem quasiCompact_of_compactSpace_to_spec_field {k : Type u} [Field k] {V : Scheme.{u}}
    [CompactSpace ↥V] (f : V ⟶ Spec (CommRingCat.of k)) : QuasiCompact f := by
  have : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstance
  refine ⟨fun W hW hW' => ?_⟩
  rcases Set.eq_empty_or_nonempty W with rfl | ⟨z, hz⟩
  · simp
  · have hW2 : W = Set.univ := Set.eq_univ_of_forall fun w => by
      rw [Subsingleton.elim w z]; exact hz
    rw [hW2]
    simpa using isCompact_univ

/- English proof (translation)
Establish `hft : RingHom.FiniteType (q.appTop).hom` using `(HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (Q := @RingHom.FiniteType) (f := q)).mp inferInstance`. Set `: Algebra ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(W', ⊤)` to `(q.appTop).hom.toAlgebra`. Establish `: Algebra.FiniteType ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(W', ⊤)` using `hft`. Establish `hk : IsNoetherianRing ↥(CommRingCat.of k)` using `inferInstanceAs (IsNoetherianRing k)`. Establish `: IsNoetherianRing ↥Γ(Spec (CommRingCat.of k), ⊤)`.

Establish `e : ↥(CommRingCat.of k) ≃+* ↥Γ(Spec (CommRingCat.of k), ⊤)` using `(Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv`. Conclude with `isNoetherianRing_of_surjective ↥(CommRingCat.of k) ↥Γ(Spec (CommRingCat.of k), ⊤) e.toRingHom e.surjective`. Establish `: IsNoetherianRing ↥Γ(W', ⊤)` using `Algebra.FiniteType.isNoetherianRing ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(W', ⊤)`. Establish `: TopologicalSpace.NoetherianSpace ↥(Spec Γ(W', ⊤))` using `inferInstanceAs (TopologicalSpace.NoetherianSpace (PrimeSpectrum ↥Γ(W', ⊤)))`. Establish `e : ↥W' ≃ₜ ↥(Spec Γ(W', ⊤))` using `TopCat.homeoOfIso (Scheme.forgetToTop.mapIso W'.isoSpec)`.

Use `⟨fun Vo hVo hVc => ?_⟩` and prove the remaining obligations. Establish `he : IsCompact (e '' (⇑g ⁻¹' Vo))` using `TopologicalSpace.NoetherianSpace.isCompact _`. Rewrite `he` using `[Homeomorph.isCompact_image]`. Then use the resulting hypothesis.
-/
private theorem quasiCompact_of_isAffine_of_locallyOfFiniteType {k : Type u} [Field k] {W' : Scheme.{u}}
    [IsAffine W'] (q : W' ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q]
    {Z : Scheme.{u}} (g : W' ⟶ Z) : QuasiCompact g := by
  have hft : RingHom.FiniteType (q.appTop).hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)
      (Q := @RingHom.FiniteType) (f := q)).mp inferInstance
  let : Algebra ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(W', ⊤) := (q.appTop).hom.toAlgebra
  have : Algebra.FiniteType ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(W', ⊤) := hft
  have hk : IsNoetherianRing ↥(CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  have : IsNoetherianRing ↥Γ(Spec (CommRingCat.of k), ⊤) := by
    have e : ↥(CommRingCat.of k) ≃+* ↥Γ(Spec (CommRingCat.of k), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    exact isNoetherianRing_of_surjective ↥(CommRingCat.of k) ↥Γ(Spec (CommRingCat.of k), ⊤)
      e.toRingHom e.surjective
  have : IsNoetherianRing ↥Γ(W', ⊤) :=
    Algebra.FiniteType.isNoetherianRing ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(W', ⊤)
  have : TopologicalSpace.NoetherianSpace ↥(Spec Γ(W', ⊤)) :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (PrimeSpectrum ↥Γ(W', ⊤)))
  have e : ↥W' ≃ₜ ↥(Spec Γ(W', ⊤)) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso W'.isoSpec)
  refine ⟨fun Vo hVo hVc => ?_⟩
  have he : IsCompact (e '' (⇑g ⁻¹' Vo)) := TopologicalSpace.NoetherianSpace.isCompact _
  rwa [Homeomorph.isCompact_image] at he

/- English proof (translation)
Use `isReduced_of_isOpenImmersion_cover (fun i => pullback.fst (pullback.snd g' (sigmaOpensDesc Y U)) (Sigma.ι (fun j => (U j).toScheme) i)) (fun i => inferInstance) ?_ ?_` and prove the remaining obligations. Introduce `i`. Establish `hoi : IsOpenImmersion (Sigma.ι (fun j => (U j).toScheme) i ≫ sigmaOpensDesc Y U)`. Rewrite using `[sigma_ι_sigmaOpensDesc]`. Use `infer_instance`.

Establish `: IsReduced (pullback g' (Sigma.ι (fun j => (U j).toScheme) i ≫ sigmaOpensDesc Y U))` using `isReduced_of_isOpenImmersion (pullback.fst g' (Sigma.ι (fun j => (U j).toScheme) i ≫ sigmaOpensDesc Y U))`. Conclude with `isReduced_of_isOpenImmersion (pullbackLeftPullbackSndIso g' (sigmaOpensDesc Y U) (Sigma.ι (fun j => (U j).toScheme) i)).hom`. Introduce `x`. Take `⟨i, y, hy⟩` from `exists_sigma_ι_base_eq (fun j => (U j).toScheme) ((pullback.snd g' (sigmaOpensDesc Y U)).base x)`. Take `⟨z, hz1, _⟩` from `Scheme.Pullback.exists_preimage_pullback (f := pullback.snd g' (sigmaOpensDesc Y U)) (g := Sigma.ι (fun j => (U j).toScheme) i) x y hy.symm`.

Conclude with `⟨i, z, hz1⟩`.
-/
theorem isReduced_pullback_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens)
    (W' : Scheme.{u}) [IsReduced W'] (g' : W' ⟶ Y) :
    IsReduced (pullback g' (sigmaOpensDesc Y U)) := by
  refine isReduced_of_isOpenImmersion_cover
    (fun i => pullback.fst (pullback.snd g' (sigmaOpensDesc Y U))
      (Sigma.ι (fun j => (U j).toScheme) i)) (fun i => inferInstance) ?_ ?_
  · intro i
    have hoi : IsOpenImmersion
        (Sigma.ι (fun j => (U j).toScheme) i ≫ sigmaOpensDesc Y U) := by
      rw [sigma_ι_sigmaOpensDesc]
      infer_instance
    have : IsReduced
        (pullback g' (Sigma.ι (fun j => (U j).toScheme) i ≫ sigmaOpensDesc Y U)) :=
      isReduced_of_isOpenImmersion
        (pullback.fst g' (Sigma.ι (fun j => (U j).toScheme) i ≫ sigmaOpensDesc Y U))
    exact isReduced_of_isOpenImmersion
      (pullbackLeftPullbackSndIso g' (sigmaOpensDesc Y U)
        (Sigma.ι (fun j => (U j).toScheme) i)).hom
  · intro x
    obtain ⟨i, y, hy⟩ :=
      exists_sigma_ι_base_eq (fun j => (U j).toScheme)
        ((pullback.snd g' (sigmaOpensDesc Y U)).base x)
    obtain ⟨z, hz1, _⟩ :=
      Scheme.Pullback.exists_preimage_pullback
        (f := pullback.snd g' (sigmaOpensDesc Y U))
        (g := Sigma.ι (fun j => (U j).toScheme) i) x y hy.symm
    exact ⟨i, z, hz1⟩

/- English proof (translation)
Establish `: IsAffine (sigmaOpens Y U)` using `isAffine_sigmaOpens Y U hU`. Establish `: CompactSpace ↥(sigmaOpens Y U)` using `inferInstance`. Establish `: QuasiCompact (pullback.snd g' (sigmaOpensDesc Y U))` using `inferInstance`. Prove the components needed by the constructor for the conclusion. Establish `hcp` using `QuasiCompact.isCompact_preimage (f := pullback.snd g' (sigmaOpensDesc Y U)) Set.univ isOpen_univ isCompact_univ`.

Simplify using `using hcp`.
-/
theorem compactSpace_pullback_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} [Finite ι]
    (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (W' : Scheme.{u}) (g' : W' ⟶ Y) [QuasiCompact g'] :
    CompactSpace ↥(pullback g' (sigmaOpensDesc Y U)) := by
  have : IsAffine (sigmaOpens Y U) := isAffine_sigmaOpens Y U hU
  have : CompactSpace ↥(sigmaOpens Y U) := inferInstance
  have : QuasiCompact (pullback.snd g' (sigmaOpensDesc Y U)) := inferInstance
  constructor
  have hcp := QuasiCompact.isCompact_preimage (f := pullback.snd g' (sigmaOpensDesc Y U))
    Set.univ isOpen_univ isCompact_univ
  simpa using hcp

/- English proof (translation)
Establish `: QuasiCompact g'` using `quasiCompact_of_isAffine_of_locallyOfFiniteType q g'`. Establish `: IsReduced (pullback g' (sigmaOpensDesc Y U))` using `isReduced_pullback_sigmaOpensDesc Y U W' g'`. Establish `: CompactSpace ↥(pullback g' (sigmaOpensDesc Y U))` using `compactSpace_pullback_sigmaOpensDesc Y U hU W' g'`. Establish `: LocallyOfFiniteType (pullback.fst g' (sigmaOpensDesc Y U))` using `inferInstance`. Establish `: LocallyOfFiniteType (pullback.fst g' (sigmaOpensDesc Y U) ≫ q)` using `inferInstance`.

Establish `: QuasiCompact (pullback.fst g' (sigmaOpensDesc Y U) ≫ q)` using `quasiCompact_of_compactSpace_to_spec_field _`. Take `⟨V, s, r, h1, h2, h3, h4, h5, h6, h7⟩` from `exists_affine_etale_cover_of_isReduced (pullback g' (sigmaOpensDesc Y U)) (pullback.fst g' (sigmaOpensDesc Y U) ≫ q)`. Conclude with `⟨V, s, r, h1, h2, h3, h4, h5, h6, h7⟩`.
-/
theorem exists_affine_etale_cover_pullback_sigmaOpensDesc {k : Type u} [Field k]
    (Y : Scheme.{u}) (p : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [QuasiCompact p]
    {ι : Type u} [Finite ι] (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (W' : Scheme.{u}) [IsAffine W'] [IsReduced W'] (q : W' ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] [QuasiCompact q] (g' : W' ⟶ Y) [Etale g'] (_hg : g' ≫ p = q) :
    ∃ (V : Scheme.{u}) (s : V ⟶ Spec (CommRingCat.of k))
      (r : V ⟶ pullback g' (sigmaOpensDesc Y U)),
      IsAffine V ∧ IsReduced V ∧ LocallyOfFiniteType s ∧ QuasiCompact s ∧
        Etale r ∧ Surjective r ∧
        r ≫ pullback.fst g' (sigmaOpensDesc Y U) ≫ q = s := by
  have : QuasiCompact g' := quasiCompact_of_isAffine_of_locallyOfFiniteType q g'
  have : IsReduced (pullback g' (sigmaOpensDesc Y U)) :=
    isReduced_pullback_sigmaOpensDesc Y U W' g'
  have : CompactSpace ↥(pullback g' (sigmaOpensDesc Y U)) :=
    compactSpace_pullback_sigmaOpensDesc Y U hU W' g'
  have : LocallyOfFiniteType (pullback.fst g' (sigmaOpensDesc Y U)) := inferInstance
  have : LocallyOfFiniteType (pullback.fst g' (sigmaOpensDesc Y U) ≫ q) := inferInstance
  have : QuasiCompact (pullback.fst g' (sigmaOpensDesc Y U) ≫ q) :=
    quasiCompact_of_compactSpace_to_spec_field _
  obtain ⟨V, s, r, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_affine_etale_cover_of_isReduced (pullback g' (sigmaOpensDesc Y U))
      (pullback.fst g' (sigmaOpensDesc Y U) ≫ q)
  exact ⟨V, s, r, h1, h2, h3, h4, h5, h6, h7⟩

/- English proof (translation)
Establish `: Etale (pullback.fst g' (sigmaOpensDesc Y U))` using `inferInstance`. Use `infer_instance`.
-/
theorem etale_comp_fst_pullback_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens)
    (W' : Scheme.{u}) (g' : W' ⟶ Y) (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Etale r] :
    Etale (r ≫ pullback.fst g' (sigmaOpensDesc Y U)) := by
  have : Etale (pullback.fst g' (sigmaOpensDesc Y U)) := inferInstance
  infer_instance

/- English proof (translation)
Establish `: Etale (pullback.snd g' (sigmaOpensDesc Y U))` using `inferInstance`. Use `infer_instance`.
-/
theorem etale_comp_snd_pullback_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens)
    (W' : Scheme.{u}) (g' : W' ⟶ Y) [Etale g'] (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Etale r] :
    Etale (r ≫ pullback.snd g' (sigmaOpensDesc Y U)) := by
  have : Etale (pullback.snd g' (sigmaOpensDesc Y U)) := inferInstance
  infer_instance

/- English proof (translation)
Use `surjective_sigmaOpensDesc Y U hU` as an intermediate fact. Establish `: Surjective (pullback.fst g' (sigmaOpensDesc Y U))` using `inferInstance`. Use `infer_instance`.
-/
theorem surjective_comp_fst_pullback_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u}
    (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (W' : Scheme.{u}) (g' : W' ⟶ Y) (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Surjective r] :
    Surjective (r ≫ pullback.fst g' (sigmaOpensDesc Y U)) := by
  have := surjective_sigmaOpensDesc Y U hU
  have : Surjective (pullback.fst g' (sigmaOpensDesc Y U)) := inferInstance
  infer_instance

/- English proof (translation)
Establish `: Surjective (pullback.snd g' (sigmaOpensDesc Y U))` using `inferInstance`. Use `infer_instance`.
-/
theorem surjective_comp_snd_pullback_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u}
    (U : ι → Y.Opens)
    (W' : Scheme.{u}) (g' : W' ⟶ Y) [Surjective g'] (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Surjective r] :
    Surjective (r ≫ pullback.snd g' (sigmaOpensDesc Y U)) := by
  have : Surjective (pullback.snd g' (sigmaOpensDesc Y U)) := inferInstance
  infer_instance

/- English proof (translation)
Rewrite using `[pullback.condition]`.
-/
theorem comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u}
    (U : ι → Y.Opens) (W' : Scheme.{u}) (g' : W' ⟶ Y) (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) :
    r ≫ pullback.fst g' (sigmaOpensDesc Y U) ≫ g' =
      r ≫ pullback.snd g' (sigmaOpensDesc Y U) ≫ sigmaOpensDesc Y U := by
  rw [pullback.condition]

end FunctorialResolution.EmbeddedResolution
