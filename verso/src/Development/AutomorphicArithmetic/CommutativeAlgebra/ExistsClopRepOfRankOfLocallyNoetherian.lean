import Mathlib
import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
import Development.AutomorphicArithmetic.CommutativeAlgebra.ClopProjFiniteEtaleOfIsClosed
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsOpenImmersionOfClosedImmersionFlatEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteLocallyFreeRepresentablePropeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw⟩`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `x ∈ m ⁻¹' Set.range u ↔ x ∈ Set.range v`. Rewrite using `[← Scheme.Pullback.range_fst]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, rfl⟩`. Use `⟨hw.isoPullback.inv b, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hw.isoPullback_inv_fst]`. Introduce and unpack `⟨a, rfl⟩`.

Use `⟨hw.isoPullback.hom a, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hw.isoPullback_hom_fst]`. Introduce `h`. Establish `hr : Set.range v = Set.range (pullback.fst m u)`. Rewrite using `[Scheme.Pullback.range_fst]`.

Use `congrArg (fun O : X'.Opens => (O : Set X')) h` as an intermediate fact. Conclude with `this.symm`. Set `e` to `IsOpenImmersion.isoOfRangeEq v (pullback.fst m u) hr`. Use `⟨e.hom ≫ pullback.snd m u, IsPullback.of_iso_pullback ⟨?_⟩ e ?_ rfl⟩` and prove the remaining obligations. Rewrite using `[← IsOpenImmersion.isoOfRangeEq_hom_fac v (pullback.fst m u) hr, Category.assoc, pullback.condition, Category.assoc]`.

Conclude with `IsOpenImmersion.isoOfRangeEq_hom_fac v (pullback.fst m u) hr`.
-/
private lemma UpperTheory.exists_isPullback_iff_preimage {V₀ X' U₀ X : Scheme.{0}} (v : V₀ ⟶ X') (m : X' ⟶ X) (u : U₀ ⟶ X)
    [IsOpenImmersion v] [IsOpenImmersion u] :
    (∃ w, IsPullback v w m u) ↔ m ⁻¹ᵁ u.opensRange = v.opensRange := by
  constructor
  · rintro ⟨w, hw⟩
    ext x
    change x ∈ m ⁻¹' Set.range u ↔ x ∈ Set.range v
    rw [← Scheme.Pullback.range_fst]
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨hw.isoPullback.inv b, ?_⟩
      rw [← Scheme.Hom.comp_apply, hw.isoPullback_inv_fst]
    · rintro ⟨a, rfl⟩
      refine ⟨hw.isoPullback.hom a, ?_⟩
      rw [← Scheme.Hom.comp_apply, hw.isoPullback_hom_fst]
  · intro h
    have hr : Set.range v = Set.range (pullback.fst m u) := by
      rw [Scheme.Pullback.range_fst]
      have := congrArg (fun O : X'.Opens => (O : Set X')) h
      exact this.symm
    let e := IsOpenImmersion.isoOfRangeEq v (pullback.fst m u) hr
    refine ⟨e.hom ≫ pullback.snd m u, IsPullback.of_iso_pullback ⟨?_⟩ e ?_ rfl⟩
    · rw [← IsOpenImmersion.isoOfRangeEq_hom_fac v (pullback.fst m u) hr, Category.assoc,
        pullback.condition, Category.assoc]
    · exact IsOpenImmersion.isoOfRangeEq_hom_fac v (pullback.fst m u) hr

/- English proof (translation)
Apply the tactic sequence `apply pullback.hom_ext <;> simp only [Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]`. Use `erw [pullback.lift_snd]`. Simplify using the standard rewrite rules. Use `erw [pullback.lift_fst]`. Simplify using the standard rewrite rules.
-/
private lemma UpperTheory.pullback_map_symmetry_whisker {S : Scheme.{0}} {T Y G : Over S} (y : T ⟶ Y) :
    pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y.left (𝟙 S) (by simp) (by simp) ≫
        (pullbackSymmetry G.hom Y.hom).hom =
      (pullbackSymmetry G.hom T.hom).hom ≫ (y ▷ G).left := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
    pullbackSymmetry_hom_comp_snd]
  · erw [pullback.lift_snd]
    simp
  · erw [pullback.lift_fst]
    simp

/- English proof (translation)
Establish `hsq` using `UpperTheory.pullback_map_symmetry_whisker (G := G) y`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply the tactic sequence `refine h.of_iso (Iso.refl _) (pullbackSymmetry G.hom T.hom) (Iso.refl _) (pullbackSymmetry G.hom Y.hom) ?_ ?_ ?_ ?_`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Conclude with `hsq`. Simplify using the standard rewrite rules. Introduce `h`. Apply the tactic sequence `refine h.of_iso (Iso.refl _) (pullbackSymmetry G.hom T.hom).symm (Iso.refl _) (pullbackSymmetry G.hom Y.hom).symm ?_ ?_ ?_ ?_`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using `only [Iso.symm_hom]`. Rewrite using `[Iso.eq_inv_comp, ← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Simplify using the standard rewrite rules.
-/
private lemma UpperTheory.isPullback_transport_symmetry {S : Scheme.{0}} {T Y G : Over S} (y : T ⟶ Y)
    (V : (T ⊗ G).left.Opens) {U₀ : Scheme.{0}} (u : U₀ ⟶ pullback G.hom Y.hom) (w : (V : Scheme.{0}) ⟶ U₀) :
    IsPullback (V.ι ≫ (pullbackSymmetry G.hom T.hom).inv) w
        (pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y.left (𝟙 S) (by simp) (by simp)) u ↔
      IsPullback V.ι w (y ▷ G).left (u ≫ (pullbackSymmetry G.hom Y.hom).hom) := by
  have hsq := UpperTheory.pullback_map_symmetry_whisker (G := G) y
  constructor
  · intro h
    refine h.of_iso (Iso.refl _) (pullbackSymmetry G.hom T.hom) (Iso.refl _)
      (pullbackSymmetry G.hom Y.hom) ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact hsq
    · simp
  · intro h
    refine h.of_iso (Iso.refl _) (pullbackSymmetry G.hom T.hom).symm (Iso.refl _)
      (pullbackSymmetry G.hom Y.hom).symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp only [Iso.symm_hom]
      rw [Iso.eq_inv_comp, ← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp

/- English proof (translation)
Introduce `S _ G hfin het r`. Take `⟨H, h, U₀, u, hprop, hcl, hfin', hflat', hrk, huniv⟩` from `GlobalTheory.T.hilbertScheme_finite_locallyFree_representable_proper S G.left G.hom hfin inferInstance inferInstance r`. Use `haveI := hprop`. Use `haveI := hcl`. Use `haveI := hfin'`.

Use `haveI := hflat'`. Use `haveI : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian h`. Use `haveI : Etale (pullback.snd G.hom h) := inferInstance`. Use `haveI : IsOpenImmersion u := UpperTheory.isOpenImmersion_of_closedImmersion_flat_etale u (pullback.snd G.hom h) inferInstance hcl hflat' inferInstance`. Set `Y : Over S` to `Over.mk h`.

Apply the tactic sequence `let ι₀ : U₀ ⟶ (Y ⊗ G).left := u ≫ (pullbackSymmetry G.hom Y.hom).hom`. Use `haveI : IsOpenImmersion ι₀ := by dsimp [ι₀]; infer_instance`. Use `haveI : IsClosedImmersion ι₀ := by dsimp [ι₀]; infer_instance`. Use `⟨Y, ι₀.opensRange, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `ι₀.isClosedEmbedding.isClosed_range`.

Introduce `y`. Establish `hp : UpperTheory.RepresentationRank.proj ι₀.opensRange = ι₀.isoOpensRange.inv ≫ (u ≫ pullback.snd G.hom h)`. Rewrite using `[Iso.eq_inv_comp]`. Express the relevant statement in the definitionally equal form `ι₀.isoOpensRange.hom ≫ (ι₀.opensRange.ι ≫ pullback.fst Y.hom G.hom) = _`. Rewrite using `[← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]`.

Simplify using `[ι₀, Y]`. Rewrite using `[hp, Scheme.Hom.finrank_comp_left_of_isIso]`. Conclude with `hrk y`. Introduce `T V hV hVr`. Take `⟨hVF, hVE⟩` from `UpperTheory.clopProj_finite_etale_of_isClosed V hfin het hV`.

Use `haveI := hVF`. Use `haveI := hVE`. Apply the tactic sequence `let v : (V : Scheme.{0}) ⟶ pullback G.hom T.hom := V.ι ≫ (pullbackSymmetry G.hom T.hom).inv`. Use `haveI : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion V.ι (by rw [Scheme.Opens.range_ι]; exact hV)`. Use `haveI : IsClosedImmersion v := by dsimp [v]; infer_instance`.

Establish `hvp : v ≫ pullback.snd G.hom T.hom = UpperTheory.RepresentationRank.proj V`. Simplify using `[v, UpperTheory.RepresentationRank.proj]`. Use `haveI : IsFinite (v ≫ pullback.snd G.hom T.hom) := by rw [hvp]; exact hVF`. Use `haveI : Flat (v ≫ pullback.snd G.hom T.hom) := by rw [hvp]; infer_instance`. Take `⟨f, ⟨hf, w, hw⟩, huniq⟩` from `huniv T.left T.hom V v inferInstance inferInstance inferInstance (fun t => by rw [hvp]; exact hVr t)`.

Establish `key : ∀ y' : T ⟶ Y, ((y' ▷ G).left ⁻¹ᵁ ι₀.opensRange = V ↔ ∃ w, IsPullback v w (pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y'.left (𝟙 S) (by simp) (by simp)) u)`. Introduce `y'`. Establish `h1` using `UpperTheory.exists_isPullback_iff_preimage V.ι (y' ▷ G).left ι₀`. Rewrite `h1` using `[Scheme.Opens.opensRange_ι]`. Rewrite using `[← h1]`.

Apply the tactic sequence `exact exists_congr fun w => (UpperTheory.isPullback_transport_symmetry y' V u w).symm`. Use `⟨Over.homMk f hf, (key _).mpr ⟨w, hw⟩, ?_⟩` and prove the remaining obligations. Introduce `y' hy'`. Take `⟨w', hw'⟩` from `(key y').mp hy'`. Conclude with `Over.OverMorphism.ext (huniq y'.left ⟨Over.w y', w', hw'⟩)`.
-/
theorem UpperTheory.exists_clopRepOfRank_of_locallyNoetherian :
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S), IsFinite G.hom → Etale G.hom → ∀ r : ℕ, ∃ (Y : Over S) (U : (Y ⊗ G).left.Opens), UpperTheory.RepresentationRank.RepOfRank r G Y U := by
  intro S _ G hfin het r
  obtain ⟨H, h, U₀, u, hprop, hcl, hfin', hflat', hrk, huniv⟩ :=
    GlobalTheory.T.hilbertScheme_finite_locallyFree_representable_proper S G.left G.hom hfin inferInstance inferInstance r
  haveI := hprop
  haveI := hcl
  haveI := hfin'
  haveI := hflat'
  haveI : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian h
  haveI : Etale (pullback.snd G.hom h) := inferInstance
  haveI : IsOpenImmersion u :=
    UpperTheory.isOpenImmersion_of_closedImmersion_flat_etale u (pullback.snd G.hom h) inferInstance hcl hflat' inferInstance
  let Y : Over S := Over.mk h
  let ι₀ : U₀ ⟶ (Y ⊗ G).left := u ≫ (pullbackSymmetry G.hom Y.hom).hom
  haveI : IsOpenImmersion ι₀ := by dsimp [ι₀]; infer_instance
  haveI : IsClosedImmersion ι₀ := by dsimp [ι₀]; infer_instance
  refine ⟨Y, ι₀.opensRange, ?_, ?_, ?_⟩
  · exact ι₀.isClosedEmbedding.isClosed_range
  · intro y
    have hp : UpperTheory.RepresentationRank.proj ι₀.opensRange = ι₀.isoOpensRange.inv ≫ (u ≫ pullback.snd G.hom h) := by
      rw [Iso.eq_inv_comp]
      change ι₀.isoOpensRange.hom ≫ (ι₀.opensRange.ι ≫ pullback.fst Y.hom G.hom) = _
      rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
      simp [ι₀, Y]
    rw [hp, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hrk y
  · intro T V hV hVr
    obtain ⟨hVF, hVE⟩ := UpperTheory.clopProj_finite_etale_of_isClosed V hfin het hV
    haveI := hVF
    haveI := hVE
    let v : (V : Scheme.{0}) ⟶ pullback G.hom T.hom := V.ι ≫ (pullbackSymmetry G.hom T.hom).inv
    haveI : IsClosedImmersion V.ι :=
      IsClosedImmersion.of_isPreimmersion V.ι (by rw [Scheme.Opens.range_ι]; exact hV)
    haveI : IsClosedImmersion v := by dsimp [v]; infer_instance
    have hvp : v ≫ pullback.snd G.hom T.hom = UpperTheory.RepresentationRank.proj V := by
      simp [v, UpperTheory.RepresentationRank.proj]
    haveI : IsFinite (v ≫ pullback.snd G.hom T.hom) := by rw [hvp]; exact hVF
    haveI : Flat (v ≫ pullback.snd G.hom T.hom) := by rw [hvp]; infer_instance
    obtain ⟨f, ⟨hf, w, hw⟩, huniq⟩ := huniv T.left T.hom V v inferInstance inferInstance
      inferInstance (fun t => by rw [hvp]; exact hVr t)
    have key : ∀ y' : T ⟶ Y, ((y' ▷ G).left ⁻¹ᵁ ι₀.opensRange = V ↔
        ∃ w, IsPullback v w
          (pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y'.left (𝟙 S) (by simp) (by simp)) u) := by
      intro y'
      have h1 := UpperTheory.exists_isPullback_iff_preimage V.ι (y' ▷ G).left ι₀
      rw [Scheme.Opens.opensRange_ι] at h1
      rw [← h1]
      exact exists_congr fun w => (UpperTheory.isPullback_transport_symmetry y' V u w).symm
    refine ⟨Over.homMk f hf, (key _).mpr ⟨w, hw⟩, ?_⟩
    intro y' hy'
    obtain ⟨w', hw'⟩ := (key y').mp hy'
    exact Over.OverMorphism.ext (huniq y'.left ⟨Over.w y', w', hw'⟩)
