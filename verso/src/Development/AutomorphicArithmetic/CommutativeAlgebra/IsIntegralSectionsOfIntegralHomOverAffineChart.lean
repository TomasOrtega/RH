import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackGamma

open CategoryTheory Limits AlgebraicGeometry

/- English proof (translation)
Introduce `A _ P Z U L u l f hu hpb O hO τ hτ ι _ hι h x`. Use `haveI := hu`. Use `haveI : IsAffineHom f := MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance`. Establish `hV : IsAffineOpen (f ⁻¹ᵁ O)` using `hO.preimage f`. Establish `hW : u ⁻¹ᵁ (f ⁻¹ᵁ O) = ι ''ᵁ ⊤`.

Apply `SetLike.coe_injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((u ≫ f) ⁻¹ᵁ O : Set Z) = _`. Rewrite using `[← hι]`. Simplify using the standard rewrite rules. Establish `hb : Function.Surjective (ι.appLE (u ⁻¹ᵁ (f ⁻¹ᵁ O)) ⊤ h).hom`.

Establish `key : ∀ (W : Z.Opens) (_ : W = ι ''ᵁ ⊤) (e : ⊤ ≤ ι ⁻¹ᵁ W), Function.Surjective (ι.appLE W ⊤ e).hom`. Introduce and unpack `W rfl e`. Establish `e2 : ι.appLE (ι ''ᵁ ⊤) ⊤ e = (ι.appIso ⊤).hom` using `(Scheme.Hom.appIso_hom' ι ⊤).symm`. Rewrite using `[e2]`. Conclude with `(ι.appIso ⊤).commRingCatIsoToRingEquiv.surjective`.

Conclude with `key _ hW h`. Establish `ha : (u.appLE (f ⁻¹ᵁ O) (u ⁻¹ᵁ (f ⁻¹ᵁ O)) le_rfl).hom.IsIntegral`. Rewrite using `[← Scheme.Hom.app_eq_appLE]`. Conclude with `IsIntegralHom.isIntegral_app u _ hV`. Use `set φ := u.appLE (f ⁻¹ᵁ O) (u ⁻¹ᵁ (f ⁻¹ᵁ O)) le_rfl ≫ ι.appLE (u ⁻¹ᵁ (f ⁻¹ᵁ O)) ⊤ h with hφ`.

Establish `hφi : φ.hom.IsIntegral`. Rewrite using `[hφ, CommRingCat.hom_comp]`. Conclude with `RingHom.IsIntegral.trans _ _ ha (RingHom.isIntegral_of_surjective _ hb)`. Use `set S := Subring.closure (Set.range ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι ≫ u ≫ l).appTop).hom ∪ {((ι ≫ u ≫ f).appLE O ⊤ h).hom τ}) with hS`. Establish `hpo` using `GroundTheory.Arith.SchemeCoh.isPushout_app_of_isPullback hpb hO`.

Establish `e1 : f.app O ≫ φ = (ι ≫ u ≫ f).appLE O ⊤ h`. Rewrite using `[hφ, Scheme.Hom.app_eq_appLE, ← Category.assoc, Scheme.Hom.appLE_comp_appLE]`. Conclude with `Scheme.Hom.appLE_comp_appLE ι (u ≫ f) O _ ⊤ _ _`. Establish `c1 : ∀ y, φ.hom ((f.app O).hom y) ∈ S`. Introduce `y`.

Establish `hy : y ∈ Subring.closure {τ}` using `hτ ▸ Subring.mem_top y`. Establish `hle : Subring.closure {τ} ≤ (S.comap φ.hom).comap (f.app O).hom`. Rewrite using `[Subring.closure_le, Set.singleton_subset_iff]`. Use `show φ.hom ((f.app O).hom τ) ∈ S`. Rewrite using `[← CommRingCat.comp_apply, e1]`.

Conclude with `Subring.subset_closure (Or.inr rfl)`. Conclude with `hle hy`. Establish `e2 : l.appLE ⊤ (f ⁻¹ᵁ O) (by simp) ≫ φ = (ι ≫ u ≫ l).appTop`. Rewrite using `[hφ]`. Use `((Scheme.Hom.appLE_comp_appLE_assoc u l ⊤ (f ⁻¹ᵁ O) (u ⁻¹ᵁ (f ⁻¹ᵁ O)) _ _ _).trans (Scheme.Hom.appLE_comp_appLE ι (u ≫ l) ⊤ _ ⊤ _ _)).trans ?_` and prove the remaining obligations.

Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Use `first`. Consider the case `rfl`. Consider the case `(congr 1; simp)`. Consider the case `simp [Scheme.Hom.appLE]`.

Establish `c2 : ∀ y, φ.hom ((l.appLE ⊤ (f ⁻¹ᵁ O) (by simp)).hom y) ∈ S`. Introduce `y`. Establish `hy : φ.hom ((l.appLE ⊤ (f ⁻¹ᵁ O) (by simp)).hom y) = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι ≫ u ≫ l).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom y)`. Rewrite using `[← CommRingCat.comp_apply, e2]`. Simplify using the standard rewrite rules.

Rewrite using `[hy]`. Conclude with `Subring.subset_closure (Or.inl ⟨_, rfl⟩)`. Use `set T := S.comap φ.hom with hT`. Set `g1` to `CommRingCat.ofHom ((f.app O).hom.codRestrict T c1)`. Set `g2` to `CommRingCat.ofHom ((l.appLE ⊤ (f ⁻¹ᵁ O) (by simp)).hom.codRestrict T c2)`.

Establish `hw : Scheme.Hom.appLE (terminal.from P) ⊤ O (by simp) ≫ g1 = Scheme.Hom.appTop (terminal.from (Spec (CommRingCat.of A))) ≫ g2`. Use extensionality with `z`. Conclude with `congrArg (fun k => k.hom z) hpo.w`. Establish `hid : hpo.desc g1 g2 hw ≫ CommRingCat.ofHom T.subtype = 𝟙 _`. Apply `hpo.hom_ext` to reduce the goal to its premises.

Rewrite using `[hpo.inl_desc_assoc, Category.comp_id]`. Use extensionality with `z`. Both sides reduce to the same expression. Rewrite using `[hpo.inr_desc_assoc, Category.comp_id]`. Use extensionality with `z`.

Both sides reduce to the same expression. Establish `hall : ∀ y, φ.hom y ∈ S`. Introduce `y`. Use `congrArg (fun k => k.hom y) hid` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this`.

Rewrite using `[← this]`. Conclude with `((hpo.desc g1 g2 hw).hom y).2`. Take `⟨p, hm, hp⟩` from `hφi x`. Use `⟨p.map (φ.hom.codRestrict S hall), hm.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`.

Conclude with `hp`.
-/
theorem UpperTheory.isIntegral_sections_of_integralHom_over_affine_chart :
    ∀ (A : Type) [CommRing A] {P Z U L : Scheme.{0}} (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A)) (f : L ⟶ P),
        IsIntegralHom u → IsPullback f l (terminal.from P) (terminal.from _) →
        ∀ (O : P.Opens), IsAffineOpen O → ∀ (τ : Γ(P, O)), Subring.closure {τ} = ⊤ →
        ∀ (ι : U ⟶ Z) [IsOpenImmersion ι], Set.range ι = ((u ≫ f) ⁻¹ᵁ O : Set Z) →
        ∀ (h : (⊤ : U.Opens) ≤ (ι ≫ u ≫ f) ⁻¹ᵁ O) (x : Γ(U, ⊤)),
          IsIntegral (Subring.closure (Set.range ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι ≫ u ≫ l).appTop).hom ∪
            {((ι ≫ u ≫ f).appLE O ⊤ h).hom τ})) x := by
  intro A _ P Z U L u l f hu hpb O hO τ hτ ι _ hι h x
  haveI := hu
  haveI : IsAffineHom f := MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  have hV : IsAffineOpen (f ⁻¹ᵁ O) := hO.preimage f
  have hW : u ⁻¹ᵁ (f ⁻¹ᵁ O) = ι ''ᵁ ⊤ := by
    apply SetLike.coe_injective
    change ((u ≫ f) ⁻¹ᵁ O : Set Z) = _
    rw [← hι]
    simp
  have hb : Function.Surjective (ι.appLE (u ⁻¹ᵁ (f ⁻¹ᵁ O)) ⊤ h).hom := by
    have key : ∀ (W : Z.Opens) (_ : W = ι ''ᵁ ⊤) (e : ⊤ ≤ ι ⁻¹ᵁ W),
        Function.Surjective (ι.appLE W ⊤ e).hom := by
      rintro W rfl e
      have e2 : ι.appLE (ι ''ᵁ ⊤) ⊤ e = (ι.appIso ⊤).hom := (Scheme.Hom.appIso_hom' ι ⊤).symm
      rw [e2]
      exact (ι.appIso ⊤).commRingCatIsoToRingEquiv.surjective
    exact key _ hW h
  have ha : (u.appLE (f ⁻¹ᵁ O) (u ⁻¹ᵁ (f ⁻¹ᵁ O)) le_rfl).hom.IsIntegral := by
    rw [← Scheme.Hom.app_eq_appLE]
    exact IsIntegralHom.isIntegral_app u _ hV
  set φ := u.appLE (f ⁻¹ᵁ O) (u ⁻¹ᵁ (f ⁻¹ᵁ O)) le_rfl ≫ ι.appLE (u ⁻¹ᵁ (f ⁻¹ᵁ O)) ⊤ h with hφ
  have hφi : φ.hom.IsIntegral := by
    rw [hφ, CommRingCat.hom_comp]
    exact RingHom.IsIntegral.trans _ _ ha (RingHom.isIntegral_of_surjective _ hb)
  set S := Subring.closure (Set.range ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    (ι ≫ u ≫ l).appTop).hom ∪ {((ι ≫ u ≫ f).appLE O ⊤ h).hom τ}) with hS
  have hpo := GroundTheory.Arith.SchemeCoh.isPushout_app_of_isPullback hpb hO
  have e1 : f.app O ≫ φ = (ι ≫ u ≫ f).appLE O ⊤ h := by
    rw [hφ, Scheme.Hom.app_eq_appLE, ← Category.assoc, Scheme.Hom.appLE_comp_appLE]
    exact Scheme.Hom.appLE_comp_appLE ι (u ≫ f) O _ ⊤ _ _
  have c1 : ∀ y, φ.hom ((f.app O).hom y) ∈ S := by
    intro y
    have hy : y ∈ Subring.closure {τ} := hτ ▸ Subring.mem_top y
    have hle : Subring.closure {τ} ≤ (S.comap φ.hom).comap (f.app O).hom := by
      rw [Subring.closure_le, Set.singleton_subset_iff]
      show φ.hom ((f.app O).hom τ) ∈ S
      rw [← CommRingCat.comp_apply, e1]
      exact Subring.subset_closure (Or.inr rfl)
    exact hle hy
  have e2 : l.appLE ⊤ (f ⁻¹ᵁ O) (by simp) ≫ φ = (ι ≫ u ≫ l).appTop := by
    rw [hφ]
    refine ((Scheme.Hom.appLE_comp_appLE_assoc u l ⊤ (f ⁻¹ᵁ O) (u ⁻¹ᵁ (f ⁻¹ᵁ O)) _ _ _).trans
      (Scheme.Hom.appLE_comp_appLE ι (u ≫ l) ⊤ _ ⊤ _ _)).trans ?_
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    first
      | rfl
      | (congr 1; simp)
      | simp [Scheme.Hom.appLE]
  have c2 : ∀ y, φ.hom ((l.appLE ⊤ (f ⁻¹ᵁ O) (by simp)).hom y) ∈ S := by
    intro y
    have hy : φ.hom ((l.appLE ⊤ (f ⁻¹ᵁ O) (by simp)).hom y) =
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι ≫ u ≫ l).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom y) := by
      rw [← CommRingCat.comp_apply, e2]
      simp
    rw [hy]
    exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
  set T := S.comap φ.hom with hT
  let g1 := CommRingCat.ofHom ((f.app O).hom.codRestrict T c1)
  let g2 := CommRingCat.ofHom ((l.appLE ⊤ (f ⁻¹ᵁ O) (by simp)).hom.codRestrict T c2)
  have hw : Scheme.Hom.appLE (terminal.from P) ⊤ O (by simp) ≫ g1 =
      Scheme.Hom.appTop (terminal.from (Spec (CommRingCat.of A))) ≫ g2 := by
    ext z
    exact congrArg (fun k => k.hom z) hpo.w
  have hid : hpo.desc g1 g2 hw ≫ CommRingCat.ofHom T.subtype = 𝟙 _ := by
    apply hpo.hom_ext
    · rw [hpo.inl_desc_assoc, Category.comp_id]
      ext z
      rfl
    · rw [hpo.inr_desc_assoc, Category.comp_id]
      ext z
      rfl
  have hall : ∀ y, φ.hom y ∈ S := by
    intro y
    have := congrArg (fun k => k.hom y) hid
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
    rw [← this]
    exact ((hpo.desc g1 g2 hw).hom y).2
  obtain ⟨p, hm, hp⟩ := hφi x
  refine ⟨p.map (φ.hom.codRestrict S hall), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hp
