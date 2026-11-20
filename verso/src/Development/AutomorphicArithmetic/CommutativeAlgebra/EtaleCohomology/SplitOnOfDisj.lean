import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitsOfSplitOn

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Establish `hgraph` using `MorphismProperty.of_isPullback (P := @IsOpenImmersion) (pullback_lift_diagonal_isPullback s f) inferInstance`. Establish `hiso : ∀ u : S ⟶ S, u = 𝟙 S → IsIso (pullback.snd u f)`. Introduce and unpack `_ rfl`. Use `infer_instance`. Use `hiso _ hs` as an intermediate fact.

Establish `h : IsOpenImmersion (pullback.lift (𝟙 S) s (by simp) ≫ pullback.snd (s ≫ f) f)` using `inferInstance`. Rewrite `h` using `[pullback.lift_snd]`. Then use the resulting hypothesis.
-/
private theorem sec_open {X S : Scheme.{0}} (f : X ⟶ S) [Etale f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) : IsOpenImmersion s := by
  have hgraph := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (pullback_lift_diagonal_isPullback s f) inferInstance
  have hiso : ∀ u : S ⟶ S, u = 𝟙 S → IsIso (pullback.snd u f) := by
    rintro _ rfl
    infer_instance
  have := hiso _ hs
  have h : IsOpenImmersion (pullback.lift (𝟙 S) s (by simp) ≫ pullback.snd (s ≫ f) f) := inferInstance
  rwa [pullback.lift_snd] at h

/- English proof (translation)
Take `⟨h, hiso⟩` from `h`. Establish `e : (t ≫ Sigma.ι (fun _ : Fin m => X) a) = t ≫ Sigma.ι (fun _ : Fin m => X) b`. Rewrite using `[← cancel_mono (Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [h i, Category.id_comp])) : ∐ (fun _ : Fin m => X) ⟶ pullback p x)]`. Simplify using `only [Category.assoc, Sigma.ι_desc]`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Simplify using `only [Category.assoc, pullback.lift_fst]`. Conclude with `ht`. Simplify using `only [Category.assoc, pullback.lift_snd]`. Use `⟨fun s => ?_⟩` and prove the remaining obligations. Establish `hd` using `disjoint_opensRange_sigmaι (fun _ : Fin m => X) a b hab`.

Establish `h1 : (t ≫ Sigma.ι (fun _ : Fin m => X) a) s ∈ (Sigma.ι (fun _ : Fin m => X) a).opensRange`. Simplify using the standard rewrite rules. Establish `h2 : (t ≫ Sigma.ι (fun _ : Fin m => X) a) s ∈ (Sigma.ι (fun _ : Fin m => X) b).opensRange`. Rewrite using `[e]`. Simplify using the standard rewrite rules.

Establish `h3` using `hd.le_bot ⟨h1, h2⟩`. Conclude with `h3`.
-/
private theorem disj_of_splitOn {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (x : X ⟶ Y) {m : ℕ} (z : Fin m → (X ⟶ Z))
    (h : SplitOn p x z) (a b : Fin m) (hab : a ≠ b) (S : Scheme.{0}) (t : S ⟶ X)
    (ht : t ≫ z a = t ≫ z b) : IsEmpty S := by
  obtain ⟨h, hiso⟩ := h
  have e : (t ≫ Sigma.ι (fun _ : Fin m => X) a) = t ≫ Sigma.ι (fun _ : Fin m => X) b := by
    rw [← cancel_mono (Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [h i, Category.id_comp])) :
      ∐ (fun _ : Fin m => X) ⟶ pullback p x)]
    simp only [Category.assoc, Sigma.ι_desc]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]; exact ht
    · simp only [Category.assoc, pullback.lift_snd]
  refine ⟨fun s => ?_⟩
  have hd := disjoint_opensRange_sigmaι (fun _ : Fin m => X) a b hab
  have h1 : (t ≫ Sigma.ι (fun _ : Fin m => X) a) s ∈ (Sigma.ι (fun _ : Fin m => X) a).opensRange := by
    simp
  have h2 : (t ≫ Sigma.ι (fun _ : Fin m => X) a) s ∈ (Sigma.ι (fun _ : Fin m => X) b).opensRange := by
    rw [e]; simp
  have h3 := hd.le_bot ⟨h1, h2⟩
  exact h3

/- English proof (translation)
Set `g` to `pullback.snd ι u`. Establish `hcl : IsClosedImmersion g` using `inferInstance`. Set `v' : Spec (CommRingCat.of U') ⟶ pullback ι u` to `pullback.lift v (Spec.map (CommRingCat.ofHom φ)) h`. Establish `hv' : v' ≫ g = Spec.map (CommRingCat.ofHom φ)` using `pullback.lift_snd _ _ _`. Take `⟨hA, hsurj⟩` from `IsClosedImmersion.isAffine_surjective_of_isAffine g`.

Establish `hinj : Function.Injective g.appTop.hom`. Establish `h0 : Function.Injective (Spec.map (CommRingCat.ofHom φ)).appTop.hom`. Establish `e` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)`. Introduce `a b hab`. Establish `h2 : ((Spec.map (CommRingCat.ofHom φ)).appTop ≫ (Scheme.ΓSpecIso _).hom).hom a = ((Spec.map (CommRingCat.ofHom φ)).appTop ≫ (Scheme.ΓSpecIso _).hom).hom b`.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply]`. Rewrite using `[hab]`. Rewrite `h2` using `[e]`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2`. Conclude with `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of U)).hom).1 (hφ h2)`.

Rewrite `h0` using `[← hv']`. Simplify using `only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp] at h0`. Conclude with `Function.Injective.of_comp h0`. Establish `hiso : IsIso g.appTop`. Rewrite using `[ConcreteCategory.isIso_iff_bijective]`.

Conclude with `⟨hinj, hsurj⟩`. Establish `hg : IsIso g`. Establish `e` using `Scheme.isoSpec_hom_naturality g`. Establish `: IsIso (g ≫ (Spec (CommRingCat.of U)).isoSpec.hom)`. Rewrite using `[← e]`.

Use `infer_instance`. Conclude with `IsIso.of_isIso_comp_right g (Spec (CommRingCat.of U)).isoSpec.hom`. Use `⟨inv g ≫ pullback.fst ι u, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]`.
-/
private theorem liftClosed {W P : Scheme.{0}} (ι : W ⟶ P) [IsClosedImmersion ι] (U U' : Type) [CommRing U] [CommRing U']
    (φ : U →+* U') (hφ : Function.Injective φ) (u : Spec (CommRingCat.of U) ⟶ P)
    (v : Spec (CommRingCat.of U') ⟶ W) (h : v ≫ ι = Spec.map (CommRingCat.ofHom φ) ≫ u) :
    ∃ w : Spec (CommRingCat.of U) ⟶ W, w ≫ ι = u := by
  let g := pullback.snd ι u
  have hcl : IsClosedImmersion g := inferInstance
  let v' : Spec (CommRingCat.of U') ⟶ pullback ι u := pullback.lift v (Spec.map (CommRingCat.ofHom φ)) h
  have hv' : v' ≫ g = Spec.map (CommRingCat.ofHom φ) := pullback.lift_snd _ _ _
  obtain ⟨hA, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine g
  have hinj : Function.Injective g.appTop.hom := by
    have h0 : Function.Injective (Spec.map (CommRingCat.ofHom φ)).appTop.hom := by
      have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
      intro a b hab
      have h2 : ((Spec.map (CommRingCat.ofHom φ)).appTop ≫ (Scheme.ΓSpecIso _).hom).hom a =
          ((Spec.map (CommRingCat.ofHom φ)).appTop ≫ (Scheme.ΓSpecIso _).hom).hom b := by
        simp only [CommRingCat.hom_comp, RingHom.comp_apply]
        rw [hab]
      rw [e] at h2
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of U)).hom).1 (hφ h2)
    rw [← hv'] at h0
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp] at h0
    exact Function.Injective.of_comp h0
  have hiso : IsIso g.appTop := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨hinj, hsurj⟩
  have hg : IsIso g := by
    have e := Scheme.isoSpec_hom_naturality g
    have : IsIso (g ≫ (Spec (CommRingCat.of U)).isoSpec.hom) := by
      rw [← e]; infer_instance
    exact IsIso.of_isIso_comp_right g (Spec (CommRingCat.of U)).isoSpec.hom
  refine ⟨inv g ≫ pullback.fst ι u, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

/- English proof (translation)
Establish `hq : QuasiCompact D.ι`. Rewrite using `[quasiCompact_iff_forall_isAffineOpen]`. Introduce `V hV`. Rewrite using `[D.ι.isOpenEmbedding.isInducing.isCompact_iff]`. Express the relevant statement in the definitionally equal form `IsCompact (D.ι '' (D.ι ⁻¹' (V : Set P)))`.

Rewrite using `[Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]`. Establish `hc : IsCompact ((V : Set P) ∩ P.basicOpen a)`. Use `(hV.basicOpen (P.presheaf.map (homOfLE le_top).op a)).isCompact` as an intermediate fact. Rewrite `this` using `[Scheme.basicOpen_res]`. Then use the resulting hypothesis. Establish `hc2` using `hc.diff D'.2`.

Use `hc2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hv, hd⟩`. Use `⟨⟨hv, ?_⟩, fun hd' => ?_⟩` and prove the remaining obligations.

Establish `: x ∈ D ⊔ D'` using `Or.inl hd`. Rewrite `this` using `[h]`. Conclude with `this`. Establish `: x ∈ D ⊓ D'` using `⟨hd, hd'⟩`. Rewrite `this` using `[h']`.

Conclude with `this`. Introduce and unpack `⟨⟨hv, hb⟩, hd'⟩`. Establish `: x ∈ D ⊔ D'` using `by rw [h]; exact hb`. Conclude with `⟨hv, this.resolve_right hd'⟩`. Use `⟨D.ι.image, D.ι.imageι, D.ι.toImage, inferInstance, D.ι.toImage_imageι, fun w hw => ?_⟩` and prove the remaining obligations.

Establish `h1 : D.ι.imageι w ∈ closure (Set.range D.ι)`. Rewrite using `[← Scheme.Hom.support_ker]`. Establish `: Set.range D.ι.imageι = D.ι.ker.support`. Conclude with `Scheme.IdealSheafData.range_subschemeι _`. Rewrite using `[← this]`.

Conclude with `⟨w, rfl⟩`. Rewrite `h1` using `[Scheme.Opens.range_ι]`. Establish `h2 : D.ι.imageι w ∈ D ⊔ D'` using `by rw [h]; exact hw`. Use `h2.resolve_right fun hd' => ?_` and prove the remaining obligations. Take `⟨y, hy, hy'⟩` from `mem_closure_iff.1 h1 D' D'.2 hd'`.

Establish `: y ∈ D' ⊓ D` using `⟨hy, hy'⟩`. Rewrite `this` using `[inf_comm, h']`. Conclude with `this`.
-/
private theorem closureOf (P : Scheme.{0}) (a : Γ(P, ⊤)) (D D' : P.Opens) (h : D ⊔ D' = P.basicOpen a)
    (h' : D ⊓ D' = ⊥) :
    ∃ (W : Scheme.{0}) (ι : W ⟶ P) (v : D.toScheme ⟶ W), IsClosedImmersion ι ∧ v ≫ ι = D.ι ∧
      ∀ w : W, ι w ∈ P.basicOpen a → ι w ∈ D := by
  have hq : QuasiCompact D.ι := by
    rw [quasiCompact_iff_forall_isAffineOpen]
    intro V hV
    rw [D.ι.isOpenEmbedding.isInducing.isCompact_iff]
    change IsCompact (D.ι '' (D.ι ⁻¹' (V : Set P)))
    rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    have hc : IsCompact ((V : Set P) ∩ P.basicOpen a) := by
      have := (hV.basicOpen (P.presheaf.map (homOfLE le_top).op a)).isCompact
      rwa [Scheme.basicOpen_res] at this
    have hc2 := hc.diff D'.2
    convert hc2 using 1
    ext x
    constructor
    · rintro ⟨hv, hd⟩
      refine ⟨⟨hv, ?_⟩, fun hd' => ?_⟩
      · have : x ∈ D ⊔ D' := Or.inl hd
        rw [h] at this; exact this
      · have : x ∈ D ⊓ D' := ⟨hd, hd'⟩
        rw [h'] at this; exact this
    · rintro ⟨⟨hv, hb⟩, hd'⟩
      have : x ∈ D ⊔ D' := by rw [h]; exact hb
      exact ⟨hv, this.resolve_right hd'⟩
  refine ⟨D.ι.image, D.ι.imageι, D.ι.toImage, inferInstance, D.ι.toImage_imageι, fun w hw => ?_⟩
  have h1 : D.ι.imageι w ∈ closure (Set.range D.ι) := by
    rw [← Scheme.Hom.support_ker]
    have : Set.range D.ι.imageι = D.ι.ker.support := by
      exact Scheme.IdealSheafData.range_subschemeι _
    rw [← this]
    exact ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι] at h1
  have h2 : D.ι.imageι w ∈ D ⊔ D' := by rw [h]; exact hw
  refine h2.resolve_right fun hd' => ?_
  obtain ⟨y, hy, hy'⟩ := mem_closure_iff.1 h1 D' D'.2 hd'
  have : y ∈ D' ⊓ D := ⟨hy, hy'⟩
  rw [inf_comm, h'] at this
  exact this

/- English proof (translation)
Use `h.map t.appTop.hom` as an intermediate fact. Simplify using `using this`.
-/
private theorem natUnit_comp {X S : Scheme.{0}} (t : S ⟶ X) (l : ℕ) (h : IsUnit (l : Γ(X, ⊤))) : IsUnit (l : Γ(S, ⊤)) := by
  have := h.map t.appTop.hom
  simpa using this

/- English proof (translation)
Establish `h1 : X.basicOpen (t.appTop.hom (l : Γ(A, ⊤))) = ⊤`. Simplify using `using Scheme.basicOpen_of_isUnit X h`. Establish `h2 : x ∈ t ⁻¹ᵁ A.basicOpen (l : Γ(A, ⊤))`. Rewrite using `[Scheme.preimage_basicOpen_top, h1]`. Discharge the goal by the elementary cases of `trivial`.

Conclude with `h2`.
-/
private theorem natUnit_mem {X A : Scheme.{0}} (t : X ⟶ A) (l : ℕ) (h : IsUnit (l : Γ(X, ⊤))) (x : X) :
    t x ∈ A.basicOpen (l : Γ(A, ⊤)) := by
  have h1 : X.basicOpen (t.appTop.hom (l : Γ(A, ⊤))) = ⊤ := by
    simpa using Scheme.basicOpen_of_isUnit X h
  have h2 : x ∈ t ⁻¹ᵁ A.basicOpen (l : Γ(A, ⊤)) := by
    rw [Scheme.preimage_basicOpen_top, h1]
    trivial
  exact h2

/- English proof (translation)
Set `Δ` to `pullback.diagonal p`. Establish `hΔ : IsOpenImmersion Δ` using `sec_open (pullback.fst p p) Δ (pullback.diagonal_fst p)`. Establish `hc : IsClosedImmersion Δ` using `inferInstance`. Set `c` to `pullback.lift f g hfg`. Establish `cf : c ≫ pullback.fst p p = f` using `pullback.lift_fst _ _ _`.

Establish `cs : c ≫ pullback.snd p p = g` using `pullback.lift_snd _ _ _`. Establish `hcl : IsClosed (Set.range Δ)` using `Δ.isClosedEmbedding.isClosed_range`. Set `R : (pullback p p).Opens` to `Δ.opensRange`. Set `R' : (pullback p p).Opens` to `⟨(Set.range Δ)ᶜ, hcl.isOpen_compl⟩`. Use `⟨c ⁻¹ᵁ R, c ⁻¹ᵁ R', ?_, ?_, fun X t => ⟨fun h => ?_, fun h x => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Distinguish the cases in `h : c x ∈ Set.range Δ`. Conclude with `Or.inl h`. Conclude with `Or.inr h`.

Rewrite using `[eq_bot_iff]`. Introduce and unpack `x ⟨h1, h2⟩`. Conclude with `(h2 h1).elim`. Establish `r : Set.range (t ≫ c) ⊆ Set.range Δ`. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `h x`. Establish `hk` using `IsOpenImmersion.lift_fac Δ (t ≫ c) r`. Generalize the expression as in `IsOpenImmersion.lift Δ (t ≫ c) r = k at hk`. Establish `e1 : k = t ≫ f`. Use `congrArg (· ≫ pullback.fst p p) hk` as an intermediate fact.

Simplify using `only [Category.assoc] at this`. Rewrite `this` using `[show Δ ≫ pullback.fst p p = 𝟙 _ from pullback.diagonal_fst p, cf, Category.comp_id]`. Conclude with `this`. Establish `e2 : k = t ≫ g`. Use `congrArg (· ≫ pullback.snd p p) hk` as an intermediate fact.

Simplify using `only [Category.assoc] at this`. Rewrite `this` using `[show Δ ≫ pullback.snd p p = 𝟙 _ from pullback.diagonal_snd p, cs, Category.comp_id]`. Conclude with `this`. Conclude with `e1.symm.trans e2`. Establish `e : t ≫ c = (t ≫ f) ≫ Δ`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, cf, show Δ ≫ pullback.fst p p = 𝟙 _ from pullback.diagonal_fst p, Category.comp_id]`. Rewrite using `[Category.assoc, Category.assoc, cs, show Δ ≫ pullback.snd p p = 𝟙 _ from pullback.diagonal_snd p, Category.comp_id, h]`. Establish `: (t ≫ c) x ∈ Set.range Δ`. Rewrite using `[e]`.

Conclude with `⟨(t ≫ f) x, by simp⟩`. Conclude with `this`.
-/
private theorem eqLocus₀ {Z Y : Scheme.{0}} (p : Z ⟶ Y) [Etale p] [IsSeparated p] (A : Scheme.{0}) (f g : A ⟶ Z)
    (hfg : f ≫ p = g ≫ p) :
    ∃ O O' : A.Opens, O ⊔ O' = ⊤ ∧ O ⊓ O' = ⊥ ∧
      ∀ (X : Scheme.{0}) (t : X ⟶ A), (∀ x, t x ∈ O) ↔ t ≫ f = t ≫ g := by
  let Δ := pullback.diagonal p
  have hΔ : IsOpenImmersion Δ := sec_open (pullback.fst p p) Δ (pullback.diagonal_fst p)
  have hc : IsClosedImmersion Δ := inferInstance
  let c := pullback.lift f g hfg
  have cf : c ≫ pullback.fst p p = f := pullback.lift_fst _ _ _
  have cs : c ≫ pullback.snd p p = g := pullback.lift_snd _ _ _
  have hcl : IsClosed (Set.range Δ) := Δ.isClosedEmbedding.isClosed_range
  let R : (pullback p p).Opens := Δ.opensRange
  let R' : (pullback p p).Opens := ⟨(Set.range Δ)ᶜ, hcl.isOpen_compl⟩
  refine ⟨c ⁻¹ᵁ R, c ⁻¹ᵁ R', ?_, ?_, fun X t => ⟨fun h => ?_, fun h x => ?_⟩⟩
  · rw [eq_top_iff]
    intro x _
    by_cases h : c x ∈ Set.range Δ
    · exact Or.inl h
    · exact Or.inr h
  · rw [eq_bot_iff]
    rintro x ⟨h1, h2⟩
    exact (h2 h1).elim
  · have r : Set.range (t ≫ c) ⊆ Set.range Δ := by
      rintro _ ⟨x, rfl⟩
      exact h x
    have hk := IsOpenImmersion.lift_fac Δ (t ≫ c) r
    generalize IsOpenImmersion.lift Δ (t ≫ c) r = k at hk
    have e1 : k = t ≫ f := by
      have := congrArg (· ≫ pullback.fst p p) hk
      simp only [Category.assoc] at this
      rw [show Δ ≫ pullback.fst p p = 𝟙 _ from pullback.diagonal_fst p, cf, Category.comp_id] at this
      exact this
    have e2 : k = t ≫ g := by
      have := congrArg (· ≫ pullback.snd p p) hk
      simp only [Category.assoc] at this
      rw [show Δ ≫ pullback.snd p p = 𝟙 _ from pullback.diagonal_snd p, cs, Category.comp_id] at this
      exact this
    exact e1.symm.trans e2
  · have e : t ≫ c = (t ≫ f) ≫ Δ := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, cf, show Δ ≫ pullback.fst p p = 𝟙 _ from pullback.diagonal_fst p,
          Category.comp_id]
      · rw [Category.assoc, Category.assoc, cs, show Δ ≫ pullback.snd p p = 𝟙 _ from pullback.diagonal_snd p,
          Category.comp_id, h]
    have : (t ≫ c) x ∈ Set.range Δ := by
      rw [e]
      exact ⟨(t ≫ f) x, by simp⟩
    exact this

/- English proof (translation)
Set `U` to `Y.basicOpen (l : Γ(Y, ⊤))`. Set `B` to `A.basicOpen (l : Γ(A, ⊤))`. Establish `hpre : ∀ h : A ⟶ Y, B ≤ h ⁻¹ᵁ U`. Introduce `h`. Rewrite using `[Scheme.preimage_basicOpen_top]`.

Simplify using `[B]`. Establish `het : Etale (T.p ∣_ U)` using `T.et`. Establish `hfin : IsFinite T.p` using `T.fin`. Establish `hsep : IsSeparated (T.p ∣_ U)` using `MorphismProperty.of_isPullback (P := @IsSeparated) (isPullback_morphismRestrict T.p U).flip inferInstance`. Establish `hf : B ≤ f ⁻¹ᵁ (T.p ⁻¹ᵁ U)` using `hpre (f ≫ T.p)`.

Establish `hg : B ≤ g ⁻¹ᵁ (T.p ⁻¹ᵁ U)` using `hpre (g ≫ T.p)`. Set `f'` to `f.resLE (T.p ⁻¹ᵁ U) B hf`. Set `g'` to `g.resLE (T.p ⁻¹ᵁ U) B hg`. Establish `hf' : f' ≫ (T.p ⁻¹ᵁ U).ι = B.ι ≫ f` using `Scheme.Hom.resLE_comp_ι _ _`. Establish `hg' : g' ≫ (T.p ⁻¹ᵁ U).ι = B.ι ≫ g` using `Scheme.Hom.resLE_comp_ι _ _`.

Establish `hfg' : f' ≫ (T.p ∣_ U) = g' ≫ (T.p ∣_ U)`. Rewrite using `[← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι, ← Category.assoc, hf', ← Category.assoc, hg', Category.assoc, Category.assoc, hfg]`. Take `⟨O₀, O₀', a, b, c⟩` from `eqLocus₀ (T.p ∣_ U) B.toScheme f' g' hfg'`. Establish `memI : ∀ (V : B.toScheme.Opens) (x : B.toScheme), B.ι x ∈ B.ι ''ᵁ V ↔ x ∈ V`. Introduce `V x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, e⟩`. Rewrite using `[← B.ι.isOpenEmbedding.injective e]` and apply the resulting hypothesis. Conclude with `fun h => ⟨x, h, rfl⟩`. Use `⟨B.ι ''ᵁ O₀, B.ι ''ᵁ O₀', ?_, ?_, fun X t hu => ?_⟩` and prove the remaining obligations.

Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, _, rfl⟩`. Conclude with `x.2`. Introduce and unpack `_ ⟨x, _, rfl⟩`.

Conclude with `x.2`. Introduce `y hy`. Set `x : B.toScheme` to `⟨y, hy⟩`. Establish `hx : x ∈ O₀ ⊔ O₀'` using `by rw [a]; trivial`. Break down `hx with hx | hx` into its components or cases.

Conclude with `Or.inl ⟨x, hx, rfl⟩`. Conclude with `Or.inr ⟨x, hx, rfl⟩`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `_ ⟨⟨x, hx, rfl⟩, hx'⟩`. Establish `h2` using `(memI _ x).1 hx'`.

Establish `: x ∈ O₀ ⊓ O₀'` using `⟨hx, h2⟩`. Rewrite `this` using `[b]`. Conclude with `this`. Establish `r : Set.range t ⊆ Set.range B.ι`. Introduce and unpack `_ ⟨x, rfl⟩`.

Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `natUnit_mem t l hu x`. Establish `hk` using `IsOpenImmersion.lift_fac B.ι t r`. Generalize the expression as in `IsOpenImmersion.lift B.ι t r = k at hk`. Substitute `hk` using the available equality.

Establish `e : (∀ x, (k ≫ B.ι) x ∈ B.ι ''ᵁ O₀) ↔ ∀ x, k x ∈ O₀` using `forall_congr' fun x => by simpa using memI O₀ (k x)`. Rewrite using `[e, c X k]`. Establish `ef : (k ≫ B.ι) ≫ f = (k ≫ f') ≫ (T.p ⁻¹ᵁ U).ι`. Rewrite using `[Category.assoc, Category.assoc, hf']`. Establish `eg : (k ≫ B.ι) ≫ g = (k ≫ g') ≫ (T.p ⁻¹ᵁ U).ι`.

Rewrite using `[Category.assoc, Category.assoc, hg']`. Rewrite using `[ef, eg]`. Conclude with `(cancel_mono _).symm`.
-/
private theorem eqLocus (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (A : Scheme.{0}) (f g : A ⟶ T.Z)
    (hfg : f ≫ T.p = g ≫ T.p) :
    ∃ O O' : A.Opens, O ⊔ O' = A.basicOpen (l : Γ(A, ⊤)) ∧ O ⊓ O' = ⊥ ∧
      ∀ (X : Scheme.{0}) (t : X ⟶ A), IsUnit (l : Γ(X, ⊤)) → ((∀ x, t x ∈ O) ↔ t ≫ f = t ≫ g) := by
  let U := Y.basicOpen (l : Γ(Y, ⊤))
  let B := A.basicOpen (l : Γ(A, ⊤))
  have hpre : ∀ h : A ⟶ Y, B ≤ h ⁻¹ᵁ U := by
    intro h
    rw [Scheme.preimage_basicOpen_top]
    simp [B]
  have het : Etale (T.p ∣_ U) := T.et
  have hfin : IsFinite T.p := T.fin
  have hsep : IsSeparated (T.p ∣_ U) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (isPullback_morphismRestrict T.p U).flip inferInstance
  have hf : B ≤ f ⁻¹ᵁ (T.p ⁻¹ᵁ U) := hpre (f ≫ T.p)
  have hg : B ≤ g ⁻¹ᵁ (T.p ⁻¹ᵁ U) := hpre (g ≫ T.p)
  let f' := f.resLE (T.p ⁻¹ᵁ U) B hf
  let g' := g.resLE (T.p ⁻¹ᵁ U) B hg
  have hf' : f' ≫ (T.p ⁻¹ᵁ U).ι = B.ι ≫ f := Scheme.Hom.resLE_comp_ι _ _
  have hg' : g' ≫ (T.p ⁻¹ᵁ U).ι = B.ι ≫ g := Scheme.Hom.resLE_comp_ι _ _
  have hfg' : f' ≫ (T.p ∣_ U) = g' ≫ (T.p ∣_ U) := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι, ← Category.assoc, hf',
      ← Category.assoc, hg', Category.assoc, Category.assoc, hfg]
  obtain ⟨O₀, O₀', a, b, c⟩ := eqLocus₀ (T.p ∣_ U) B.toScheme f' g' hfg'
  have memI : ∀ (V : B.toScheme.Opens) (x : B.toScheme), B.ι x ∈ B.ι ''ᵁ V ↔ x ∈ V := by
    intro V x
    constructor
    · rintro ⟨y, hy, e⟩
      rwa [← B.ι.isOpenEmbedding.injective e]
    · exact fun h => ⟨x, h, rfl⟩
  refine ⟨B.ι ''ᵁ O₀, B.ι ''ᵁ O₀', ?_, ?_, fun X t hu => ?_⟩
  · apply le_antisymm
    · refine sup_le ?_ ?_
      · rintro _ ⟨x, _, rfl⟩
        exact x.2
      · rintro _ ⟨x, _, rfl⟩
        exact x.2
    · intro y hy
      let x : B.toScheme := ⟨y, hy⟩
      have hx : x ∈ O₀ ⊔ O₀' := by rw [a]; trivial
      rcases hx with hx | hx
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr ⟨x, hx, rfl⟩
  · rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, hx'⟩
    have h2 := (memI _ x).1 hx'
    have : x ∈ O₀ ⊓ O₀' := ⟨hx, h2⟩
    rw [b] at this
    exact this
  · have r : Set.range t ⊆ Set.range B.ι := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact natUnit_mem t l hu x
    have hk := IsOpenImmersion.lift_fac B.ι t r
    generalize IsOpenImmersion.lift B.ι t r = k at hk
    subst hk
    have e : (∀ x, (k ≫ B.ι) x ∈ B.ι ''ᵁ O₀) ↔ ∀ x, k x ∈ O₀ :=
      forall_congr' fun x => by simpa using memI O₀ (k x)
    rw [e, c X k]
    have ef : (k ≫ B.ι) ≫ f = (k ≫ f') ≫ (T.p ⁻¹ᵁ U).ι := by
      rw [Category.assoc, Category.assoc, hf']
    have eg : (k ≫ B.ι) ≫ g = (k ≫ g') ≫ (T.p ⁻¹ᵁ U).ι := by
      rw [Category.assoc, Category.assoc, hg']
    rw [ef, eg]
    exact (cancel_mono _).symm

/- English proof (translation)
Set `U` to `Y.basicOpen (l : Γ(Y, ⊤))`. Establish `het : Etale (T.p ∣_ U)` using `T.et`. Establish `r : Set.range x ⊆ Set.range U.ι`. Introduce and unpack `_ ⟨u, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Conclude with `natUnit_mem x l hl u`. Establish `hk` using `IsOpenImmersion.lift_fac U.ι x r`. Generalize the expression as in `IsOpenImmersion.lift U.ι x r = x' at hk`. Substitute `hk` using the available equality. Establish `sq` using `(IsPullback.of_hasPullback (T.p ∣_ U) x').paste_horiz (isPullback_morphismRestrict T.p U).flip`.

Establish `h1 : Etale (pullback.snd (T.p ∣_ U) x')` using `inferInstance`. Establish `e : pullback.snd T.p (x' ≫ U.ι) = sq.isoPullback.inv ≫ pullback.snd (T.p ∣_ U) x'`. Rewrite using `[Iso.eq_inv_comp]`. Conclude with `sq.isoPullback_hom_snd`. Rewrite using `[e]`.

Use `infer_instance`.
-/
private theorem etale_snd (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (X : Scheme.{0}) (x : X ⟶ Y)
    (hl : IsUnit (l : Γ(X, ⊤))) : Etale (pullback.snd T.p x) := by
  let U := Y.basicOpen (l : Γ(Y, ⊤))
  have het : Etale (T.p ∣_ U) := T.et
  have r : Set.range x ⊆ Set.range U.ι := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact natUnit_mem x l hl u
  have hk := IsOpenImmersion.lift_fac U.ι x r
  generalize IsOpenImmersion.lift U.ι x r = x' at hk
  subst hk
  have sq := (IsPullback.of_hasPullback (T.p ∣_ U) x').paste_horiz (isPullback_morphismRestrict T.p U).flip
  have h1 : Etale (pullback.snd (T.p ∣_ U) x') := inferInstance
  have e : pullback.snd T.p (x' ≫ U.ι) = sq.isoPullback.inv ≫ pullback.snd (T.p ∣_ U) x' := by
    rw [Iso.eq_inv_comp]
    exact sq.isoPullback_hom_snd
  rw [e]
  infer_instance

/- English proof (translation)
Establish `ho : IsOpenImmersion σ` using `sec_open q σ hσ`. Set `V : X.Opens` to `τ ⁻¹ᵁ σ.opensRange`. Use `⟨V, ⟨u, h⟩, ?_⟩` and prove the remaining obligations. Establish `r : Set.range (V.ι ≫ τ) ⊆ Set.range σ`. Introduce and unpack `_ ⟨v, rfl⟩`.

Conclude with `v.2`. Establish `hk` using `IsOpenImmersion.lift_fac σ (V.ι ≫ τ) r`. Generalize the expression as in `IsOpenImmersion.lift σ (V.ι ≫ τ) r = k at hk`. Establish `e : k = V.ι`. Use `congrArg (· ≫ q) hk` as an intermediate fact.

Simplify using `only [Category.assoc, hσ, hτ, Category.comp_id] at this`. Conclude with `this`. Rewrite using `[← hk, e]`.
-/
private theorem sec_agree {Q X : Scheme.{0}} (q : Q ⟶ X) [Etale q] (σ τ : X ⟶ Q) (hσ : σ ≫ q = 𝟙 X) (hτ : τ ≫ q = 𝟙 X)
    (u : X) (h : σ u = τ u) : ∃ V : X.Opens, u ∈ V ∧ V.ι ≫ σ = V.ι ≫ τ := by
  have ho : IsOpenImmersion σ := sec_open q σ hσ
  let V : X.Opens := τ ⁻¹ᵁ σ.opensRange
  refine ⟨V, ⟨u, h⟩, ?_⟩
  have r : Set.range (V.ι ≫ τ) ⊆ Set.range σ := by
    rintro _ ⟨v, rfl⟩
    exact v.2
  have hk := IsOpenImmersion.lift_fac σ (V.ι ≫ τ) r
  generalize IsOpenImmersion.lift σ (V.ι ≫ τ) r = k at hk
  have e : k = V.ι := by
    have := congrArg (· ≫ q) hk
    simp only [Category.assoc, hσ, hτ, Category.comp_id] at this
    exact this
  rw [← hk, e]

/- English proof (translation)
Establish `hu : IsUnit (l : Γ(Spec (CommRingCat.of K), ⊤))`. Use `(IsUnit.mk0 _ hK).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom` as an intermediate fact. Simplify using `using this`. Establish `het` using `etale_snd l Y T _ y hu`. Establish `hfin : IsFinite T.p` using `T.fin`.

Set `r` to `pullback.snd T.p y`. Establish `hr : IsFinite r` using `inferInstance`. Set `pt : Spec (CommRingCat.of K)` to `IsLocalRing.closedPoint K`. Establish `hsub : ∀ a b : Spec (CommRingCat.of K), a = b` using `fun a b => Subsingleton.elim a b`. Establish `hF : Finite (pullback T.p y : Scheme.{0})`.

Establish `h0` using `r.finite_preimage_singleton pt`. Establish `: r ⁻¹' {pt} = Set.univ` using `Set.eq_univ_of_forall fun a => hsub _ _`. Rewrite `h0` using `[this]`. Conclude with `Set.finite_univ_iff.1 h0`. Set `F : {z : Spec (CommRingCat.of K) ⟶ T.Z // z ≫ T.p = y} → (pullback T.p y : Scheme.{0})` to `fun z => pullback.lift z.1 (𝟙 _) (by rw [z.2, Category.id_comp]) pt`.

Use `Finite.of_injective F fun a b hab => ?_` and prove the remaining obligations. Take `⟨V, hV, e⟩` from `sec_agree r _ _ (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) pt hab`. Establish `hVt : V = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Rewrite using `[hsub x pt]` and apply the resulting hypothesis. Substitute `hVt` using the available equality. Establish `e2` using `congrArg (· ≫ pullback.fst T.p y) e`. Simplify using `only [Category.assoc, pullback.lift_fst] at e2`. Establish `hiso : IsIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι` using `isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)`.

Conclude with `Subtype.ext ((cancel_epi _).1 e2)`.
-/
private theorem finite_sec (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (K : Type) [Field K] (hK : (l : K) ≠ 0)
    (y : Spec (CommRingCat.of K) ⟶ Y) :
    Finite {z : Spec (CommRingCat.of K) ⟶ T.Z // z ≫ T.p = y} := by
  have hu : IsUnit (l : Γ(Spec (CommRingCat.of K), ⊤)) := by
    have := (IsUnit.mk0 _ hK).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    simpa using this
  have het := etale_snd l Y T _ y hu
  have hfin : IsFinite T.p := T.fin
  let r := pullback.snd T.p y
  have hr : IsFinite r := inferInstance
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hsub : ∀ a b : Spec (CommRingCat.of K), a = b := fun a b => Subsingleton.elim a b
  have hF : Finite (pullback T.p y : Scheme.{0}) := by
    have h0 := r.finite_preimage_singleton pt
    have : r ⁻¹' {pt} = Set.univ := Set.eq_univ_of_forall fun a => hsub _ _
    rw [this] at h0
    exact Set.finite_univ_iff.1 h0
  let F : {z : Spec (CommRingCat.of K) ⟶ T.Z // z ≫ T.p = y} → (pullback T.p y : Scheme.{0}) := fun z =>
    pullback.lift z.1 (𝟙 _) (by rw [z.2, Category.id_comp]) pt
  refine Finite.of_injective F fun a b hab => ?_
  obtain ⟨V, hV, e⟩ := sec_agree r _ _ (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) pt hab
  have hVt : V = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rwa [hsub x pt]
  subst hVt
  have e2 := congrArg (· ≫ pullback.fst T.p y) e
  simp only [Category.assoc, pullback.lift_fst] at e2
  have hiso : IsIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  exact Subtype.ext ((cancel_epi _).1 e2)

/- English proof (translation)
Set `κ` to `Q.residueField ζ`. Set `K` to `AlgebraicClosure κ`. Use `⟨K, inferInstance, inferInstance, Spec.map (CommRingCat.ofHom (algebraMap κ K)) ≫ Q.fromSpecResidueField ζ, IsLocalRing.closedPoint K, ?_⟩` and prove the remaining obligations. Conclude with `Q.fromSpecResidueField_apply ζ _`.
-/
private theorem exists_geom (Q : Scheme.{0}) (ζ : Q) : ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K)
    (g : Spec (CommRingCat.of K) ⟶ Q) (pt : Spec (CommRingCat.of K)), g pt = ζ := by
  let κ := Q.residueField ζ
  let K := AlgebraicClosure κ
  refine ⟨K, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap κ K)) ≫ Q.fromSpecResidueField ζ, IsLocalRing.closedPoint K, ?_⟩
  exact Q.fromSpecResidueField_apply ζ _

/- English proof (translation)
Use `⟨hz, ?_⟩` and prove the remaining obligations. Establish `het` using `etale_snd l Y T X x hl`. Set `q` to `pullback.snd T.p x`. Set `σ : ∀ i, X ⟶ pullback T.p x` to `fun i => pullback.lift (z i) (𝟙 X) (by rw [hz i, Category.id_comp])`. Establish `hσq : ∀ i, σ i ≫ q = 𝟙 X` using `fun i => pullback.lift_snd _ _ _`.

Establish `hσf : ∀ i, σ i ≫ pullback.fst T.p x = z i` using `fun i => pullback.lift_fst _ _ _`. Establish `ho : ∀ i, IsOpenImmersion (σ i)` using `fun i => sec_open q (σ i) (hσq i)`. Establish `hpts : ∀ i (u : X), q (σ i u) = u` using `fun i u => by`. Use `congrArg (fun k : X ⟶ X => k u) (hσq i)` as an intermediate fact. Simplify using `using this`.

Establish `hdis : _root_.Pairwise (Function.onFun Disjoint fun i => Set.range (σ i))`. Introduce `a b hab`. Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce and unpack `_ ⟨u, rfl⟩ ⟨v, e⟩`. Establish `huv : v = u`.

Use `congrArg q e` as an intermediate fact. Rewrite `this` using `[hpts, hpts]`. Then use the resulting hypothesis. Substitute `huv` using the available equality. Take `⟨V, hV, e2⟩` from `sec_agree q (σ b) (σ a) (hσq b) (hσq a) v e`. Establish `e3` using `congrArg (· ≫ pullback.fst T.p x) e2`.

Simplify using `only [Category.assoc, hσf] at e3`. Conclude with `(hd a b hab V.toScheme V.ι e3.symm).false ⟨v, hV⟩`. Establish `hopen : IsOpenImmersion (Sigma.desc σ)` using `isOpenImmersion_sigmaDesc _ σ hdis`. Use `isIso_of_isOpenImmersion_of_opensRange_eq_top _ (TopologicalSpace.Opens.ext ?_)` and prove the remaining obligations. Use `Set.eq_univ_of_forall fun ζ => ?_` and prove the remaining obligations.

Take `⟨K, _, _, g, pt, hg⟩` from `exists_geom _ ζ`. Set `e` to `g ≫ q`. Establish `hK : (l : K) ≠ 0`. Establish `h1` using `natUnit_comp e l hl`. Establish `h2` using `h1.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom`.

Establish `h3 : IsUnit (l : K)` using `by simpa using h2`. Conclude with `h3.ne_zero`. Establish `hfin` using `finite_sec l Y T K hK (e ≫ x)`. Establish `hcard` using `T.deg K hK (e ≫ x)`. Set `F : Fin T.d → {w : Spec (CommRingCat.of K) ⟶ T.Z // w ≫ T.p = e ≫ x}` to `fun i => ⟨e ≫ z i, by rw [Category.assoc, hz i]⟩`.

Establish `hinj : Function.Injective F`. Introduce `a b hab`. Assume the negation of the conclusion as `hne`. Conclude with `(hd a b hne _ e (congrArg Subtype.val hab)).false pt`. Establish `hbij` using `hinj.bijective_of_nat_card_le (by rw [hcard]; simp)`.

Take `⟨i, hi⟩` from `hbij.2 ⟨g ≫ pullback.fst T.p x, by`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]⟩`. Establish `hi' : e ≫ z i = g ≫ pullback.fst T.p x` using `congrArg Subtype.val hi`. Establish `hgi : g = e ≫ σ i`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, hσf, hi']`. Rewrite using `[Category.assoc]`. Express the relevant statement in the definitionally equal form `g ≫ q = e ≫ σ i ≫ q`. Rewrite using `[hσq, Category.comp_id]`. Use `⟨Sigma.ι (fun _ : Fin T.d => X) i (e pt), ?_⟩` and prove the remaining obligations.

Rewrite using `[← hg, hgi]`. Establish `: Sigma.ι (fun _ : Fin T.d => X) i ≫ Sigma.desc σ = σ i` using `Sigma.ι_desc _ _`. Simplify using `only [Scheme.Hom.comp_apply]`. Rewrite using `[← Scheme.Hom.comp_apply, this]`.
-/
private theorem splitOn_of_disj (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (X : Scheme.{0}) (x : X ⟶ Y)
    (z : Fin T.d → (X ⟶ T.Z)) (hz : ∀ i, z i ≫ T.p = x) (hl : IsUnit (l : Γ(X, ⊤)))
    (hd : ∀ a b, a ≠ b → ∀ (S : Scheme.{0}) (t : S ⟶ X), t ≫ z a = t ≫ z b → IsEmpty S) :
    SplitOn T.p x z := by
  refine ⟨hz, ?_⟩
  have het := etale_snd l Y T X x hl
  let q := pullback.snd T.p x
  let σ : ∀ i, X ⟶ pullback T.p x := fun i => pullback.lift (z i) (𝟙 X) (by rw [hz i, Category.id_comp])
  have hσq : ∀ i, σ i ≫ q = 𝟙 X := fun i => pullback.lift_snd _ _ _
  have hσf : ∀ i, σ i ≫ pullback.fst T.p x = z i := fun i => pullback.lift_fst _ _ _
  have ho : ∀ i, IsOpenImmersion (σ i) := fun i => sec_open q (σ i) (hσq i)
  have hpts : ∀ i (u : X), q (σ i u) = u := fun i u => by
    have := congrArg (fun k : X ⟶ X => k u) (hσq i)
    simpa using this
  have hdis : _root_.Pairwise (Function.onFun Disjoint fun i => Set.range (σ i)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨u, rfl⟩ ⟨v, e⟩
    have huv : v = u := by
      have := congrArg q e
      rwa [hpts, hpts] at this
    subst huv
    obtain ⟨V, hV, e2⟩ := sec_agree q (σ b) (σ a) (hσq b) (hσq a) v e
    have e3 := congrArg (· ≫ pullback.fst T.p x) e2
    simp only [Category.assoc, hσf] at e3
    exact (hd a b hab V.toScheme V.ι e3.symm).false ⟨v, hV⟩
  have hopen : IsOpenImmersion (Sigma.desc σ) := isOpenImmersion_sigmaDesc _ σ hdis
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (TopologicalSpace.Opens.ext ?_)
  refine Set.eq_univ_of_forall fun ζ => ?_
  obtain ⟨K, _, _, g, pt, hg⟩ := exists_geom _ ζ
  let e := g ≫ q
  have hK : (l : K) ≠ 0 := by
    have h1 := natUnit_comp e l hl
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    have h3 : IsUnit (l : K) := by simpa using h2
    exact h3.ne_zero
  have hfin := finite_sec l Y T K hK (e ≫ x)
  have hcard := T.deg K hK (e ≫ x)
  let F : Fin T.d → {w : Spec (CommRingCat.of K) ⟶ T.Z // w ≫ T.p = e ≫ x} := fun i =>
    ⟨e ≫ z i, by rw [Category.assoc, hz i]⟩
  have hinj : Function.Injective F := by
    intro a b hab
    by_contra hne
    exact (hd a b hne _ e (congrArg Subtype.val hab)).false pt
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard]; simp)
  obtain ⟨i, hi⟩ := hbij.2 ⟨g ≫ pullback.fst T.p x, by
    rw [Category.assoc, pullback.condition, ← Category.assoc]⟩
  have hi' : e ≫ z i = g ≫ pullback.fst T.p x := congrArg Subtype.val hi
  have hgi : g = e ≫ σ i := by
    apply pullback.hom_ext
    · rw [Category.assoc, hσf, hi']
    · rw [Category.assoc]
      change g ≫ q = e ≫ σ i ≫ q
      rw [hσq, Category.comp_id]
  refine ⟨Sigma.ι (fun _ : Fin T.d => X) i (e pt), ?_⟩
  rw [← hg, hgi]
  have : Sigma.ι (fun _ : Fin T.d => X) i ≫ Sigma.desc σ = σ i := Sigma.ι_desc _ _
  simp only [Scheme.Hom.comp_apply]
  rw [← Scheme.Hom.comp_apply, this]

/- English proof (translation)
Establish `h : IsUnit (l : Localization.Away (l : U))`. Use `IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (l : U)) (l : U)` as an intermediate fact. Simplify using `using this`. Use `h.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (l : U)))).inv.hom` as an intermediate fact. Simplify using `using this`.
-/
private theorem natUnit_away (l : ℕ) (U : Type) [CommRing U] :
    IsUnit (l : Γ(Spec (CommRingCat.of (Localization.Away (l : U))), ⊤)) := by
  have h : IsUnit (l : Localization.Away (l : U)) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (l : U)) (l : U)
    simpa using this
  have := h.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (l : U)))).inv.hom
  simpa using this

/- English proof (translation)
The claim follows from `IsLocalization.injective _ (Submonoid.powers_le.2 h)`.
-/
private theorem away_inj (l : ℕ) (U : Type) [CommRing U] (h : (l : U) ∈ nonZeroDivisors U) :
    Function.Injective (algebraMap U (Localization.Away (l : U))) :=
  IsLocalization.injective _ (Submonoid.powers_le.2 h)

/- English proof (translation)
Introduce `l Y J _ T`. Set `I` to `Σ j, Fin (T j).d`. Set `Zi : I → Scheme.{0}` to `fun i => (T i.1).Z`. Set `pi : ∀ i, Zi i ⟶ Y` to `fun i => (T i.1).p`. Set `P : Scheme.{0}` to `widePullback Y Zi pi`.

Set `c : ∀ i, P ⟶ Zi i` to `WidePullback.π pi`. Set `π₀ : P ⟶ Y` to `WidePullback.base pi`. Establish `hc : ∀ i, c i ≫ pi i = π₀` using `WidePullback.π_arrow pi`. Set `Q` to `{q : Σ j, Fin (T j).d × Fin (T j).d // q.2.1 ≠ q.2.2}`. Establish `hE : ∀ q : Q, ∃ O O' : P.Opens, O ⊔ O' = P.basicOpen (l : Γ(P, ⊤)) ∧ O ⊓ O' = ⊥ ∧ ∀ (X : Scheme.{0}) (t : X ⟶ P), IsUnit (l : Γ(X, ⊤)) → ((∀ x, t x ∈ O) ↔ t ≫ c ⟨q.1.1, q.1.2.1⟩ = t ≫ c ⟨q.1.1, q.1.2.2⟩)` using `fun q => eqLocus l Y (T q.1.1) P (c ⟨q.1.1, q.1.2.1⟩) (c ⟨q.1.1, q.1.2.2⟩) ((hc ⟨q.1.1, q.1.2.1⟩).trans (hc ⟨q.1.1, q.1.2.2⟩).symm)`.

Use `choose O O' h1 h2 h3 using hE`. Set `B` to `P.basicOpen (l : Γ(P, ⊤))`. Establish `hOB : ∀ q, O q ≤ B` using `fun q => le_sup_left.trans_eq (h1 q)`. Establish `hOB' : ∀ q, O' q ≤ B` using `fun q => le_sup_right.trans_eq (h1 q)`. Set `D : P.Opens` to `⟨(B : Set P) ∩ ⋂ q, (O' q : Set P), B.2.inter (isOpen_iInter_of_finite fun q => (O' q).2)⟩`.

Set `D' : P.Opens` to `⨆ q, O q`. Establish `memD : ∀ x, x ∈ D ↔ x ∈ B ∧ ∀ q, x ∉ O q`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hb, hq⟩`.

Use `⟨hb, fun q hx => ?_⟩` and prove the remaining obligations. Establish `: x ∈ O q ⊓ O' q` using `⟨hx, Set.mem_iInter.1 hq q⟩`. Rewrite `this` using `[h2 q]`. Conclude with `this`. Introduce and unpack `⟨hb, hq⟩`.

Use `⟨hb, Set.mem_iInter.2 fun q => ?_⟩` and prove the remaining obligations. Establish `: x ∈ O q ⊔ O' q` using `by rw [h1 q]; exact hb`. Conclude with `this.resolve_left (hq q)`. Establish `hDD : D ⊔ D' = B`. Apply `le_antisymm` to reduce the goal to its premises.

Use `sup_le (fun x hx => ((memD x).1 hx).1) (iSup_le hOB)` and prove the remaining obligations. Introduce `x hx`. Distinguish the cases in `h : ∀ q, x ∉ O q`. Conclude with `Or.inl ((memD x).2 ⟨hx, h⟩)`. Use `push_neg at h`.

Take `⟨q, hq⟩` from `h`. Conclude with `Or.inr ((le_iSup O q) hq)`. Establish `hDD' : D ⊓ D' = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `x ⟨hx, hx'⟩`.

Take `⟨q, hq⟩` from `(Opens.mem_iSup).1 hx'`. Conclude with `((memD x).1 hx).2 q hq`. Take `⟨W, ι, vD, hcl, hvD, hWD⟩` from `closureOf P (l : Γ(P, ⊤)) D D' hDD hDD'`. Use `⟨⟨W, ι ≫ π₀, fun j i => ι ≫ c ⟨j, i⟩, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `j i`.

Rewrite using `[Category.assoc]`. Conclude with `congrArg (ι ≫ ·) (hc ⟨j, i⟩)`. Introduce `X w hu j`. Use `splitOn_of_disj l Y (T j) X _ _ (fun i => ?_) hu ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc]`.

Conclude with `congrArg (fun k => w ≫ ι ≫ k) (hc ⟨j, i⟩)`. Introduce `a b hab S t ht`. Assume the negation of the conclusion as `hS`. Take `⟨pt⟩` from `not_isEmpty_iff.1 hS`. Set `q : Q` to `⟨⟨j, a, b⟩, hab⟩`.

Establish `hu' : IsUnit (l : Γ(S, ⊤))` using `natUnit_comp t l hu`. Establish `key` using `(h3 q S (t ≫ w ≫ ι) hu').2 (by simpa [Category.assoc] using ht) pt`. Establish `hb : ι (w (t pt)) ∈ B`. Use `natUnit_mem (w ≫ ι) l hu (t pt)` as an intermediate fact. Simplify using `using this`.

Establish `hD` using `hWD _ hb`. Use `((memD _).1 hD).2 q ?_` and prove the remaining obligations. Simplify using `using key`. Introduce `U _ hl y z hz hsp`. Set `u : Spec (CommRingCat.of U) ⟶ P` to `WidePullback.lift y (fun i => z i.1 i.2) (fun i => hz i.1 i.2)`.

Establish `hu₀ : u ≫ π₀ = y` using `WidePullback.lift_base _ _ _ _`. Establish `huc : ∀ i, u ≫ c i = z i.1 i.2` using `fun i => WidePullback.lift_π _ _ _ _ _`. Set `a` to `awayPt l U`. Establish `hau : IsUnit (l : Γ(Spec (CommRingCat.of (Localization.Away (l : U))), ⊤))` using `natUnit_away l U`. Establish `hrange : ∀ x, (a ≫ u) x ∈ D`.

Introduce `x`. Use `(memD _).2 ⟨natUnit_mem _ l hau x, fun q hq => ?_⟩` and prove the remaining obligations. Set `V : (Spec (CommRingCat.of (Localization.Away (l : U)))).Opens` to `(a ≫ u) ⁻¹ᵁ O q`. Establish `hV : ∀ v, (V.ι ≫ a ≫ u) v ∈ O q`. Introduce `v`.

Conclude with `v.2`. Establish `e` using `(h3 q V.toScheme (V.ι ≫ a ≫ u) (natUnit_comp V.ι l hau)).1 hV`. Establish `e' : V.ι ≫ a ≫ z q.1.1 q.1.2.1 = V.ι ≫ a ≫ z q.1.1 q.1.2.2`. Establish `e1` using `huc ⟨q.1.1, q.1.2.1⟩`. Establish `e2` using `huc ⟨q.1.1, q.1.2.2⟩`.

Simplify using `only [Category.assoc] at e`. Rewrite `e` using `[e1, e2]`. Conclude with `e`. Use `disj_of_splitOn _ _ _ (hsp q.1.1) _ _ q.2 V.toScheme V.ι (by simpa [Category.assoc] using e')` as an intermediate fact. Conclude with `this.false ⟨x, hq⟩`.

Establish `hr : Set.range (a ≫ u) ⊆ Set.range D.ι`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hrange x`. Set `v₀` to `IsOpenImmersion.lift D.ι (a ≫ u) hr`.

Establish `hv₀ : v₀ ≫ D.ι = a ≫ u` using `IsOpenImmersion.lift_fac _ _ _`. Take `⟨w, hw⟩` from `liftClosed ι U (Localization.Away (l : U)) (algebraMap U _) (away_inj l U hl) u (v₀ ≫ vD) (by rw [Category.assoc, hvD, hv₀])`. Use `⟨w, ⟨?_, fun j i => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, hw, hu₀]`. Rewrite using `[← Category.assoc, hw]`.

Conclude with `huc ⟨j, i⟩`. Introduce and unpack `w' ⟨e1, e2⟩`. Rewrite using `[← cancel_mono ι, hw]`. Use `WidePullback.hom_ext pi _ _ (fun i => ?_) ?_` and prove the remaining obligations. Use `e2 i.1 i.2` as an intermediate fact.

Rewrite using `[Category.assoc]`. Conclude with `this.trans (huc i).symm`. Rewrite using `[Category.assoc]`. Conclude with `e1.trans hu₀.symm`.
-/
theorem wEx : WEx := by
  intro l Y J _ T
  let I := Σ j, Fin (T j).d
  let Zi : I → Scheme.{0} := fun i => (T i.1).Z
  let pi : ∀ i, Zi i ⟶ Y := fun i => (T i.1).p
  let P : Scheme.{0} := widePullback Y Zi pi
  let c : ∀ i, P ⟶ Zi i := WidePullback.π pi
  let π₀ : P ⟶ Y := WidePullback.base pi
  have hc : ∀ i, c i ≫ pi i = π₀ := WidePullback.π_arrow pi
  let Q := {q : Σ j, Fin (T j).d × Fin (T j).d // q.2.1 ≠ q.2.2}
  have hE : ∀ q : Q, ∃ O O' : P.Opens, O ⊔ O' = P.basicOpen (l : Γ(P, ⊤)) ∧ O ⊓ O' = ⊥ ∧
      ∀ (X : Scheme.{0}) (t : X ⟶ P), IsUnit (l : Γ(X, ⊤)) →
        ((∀ x, t x ∈ O) ↔ t ≫ c ⟨q.1.1, q.1.2.1⟩ = t ≫ c ⟨q.1.1, q.1.2.2⟩) := fun q =>
    eqLocus l Y (T q.1.1) P (c ⟨q.1.1, q.1.2.1⟩) (c ⟨q.1.1, q.1.2.2⟩)
      ((hc ⟨q.1.1, q.1.2.1⟩).trans (hc ⟨q.1.1, q.1.2.2⟩).symm)
  choose O O' h1 h2 h3 using hE
  let B := P.basicOpen (l : Γ(P, ⊤))
  have hOB : ∀ q, O q ≤ B := fun q => le_sup_left.trans_eq (h1 q)
  have hOB' : ∀ q, O' q ≤ B := fun q => le_sup_right.trans_eq (h1 q)
  let D : P.Opens := ⟨(B : Set P) ∩ ⋂ q, (O' q : Set P), B.2.inter (isOpen_iInter_of_finite fun q => (O' q).2)⟩
  let D' : P.Opens := ⨆ q, O q
  have memD : ∀ x, x ∈ D ↔ x ∈ B ∧ ∀ q, x ∉ O q := by
    intro x
    constructor
    · rintro ⟨hb, hq⟩
      refine ⟨hb, fun q hx => ?_⟩
      have : x ∈ O q ⊓ O' q := ⟨hx, Set.mem_iInter.1 hq q⟩
      rw [h2 q] at this
      exact this
    · rintro ⟨hb, hq⟩
      refine ⟨hb, Set.mem_iInter.2 fun q => ?_⟩
      have : x ∈ O q ⊔ O' q := by rw [h1 q]; exact hb
      exact this.resolve_left (hq q)
  have hDD : D ⊔ D' = B := by
    apply le_antisymm
    · refine sup_le (fun x hx => ((memD x).1 hx).1) (iSup_le hOB)
    · intro x hx
      by_cases h : ∀ q, x ∉ O q
      · exact Or.inl ((memD x).2 ⟨hx, h⟩)
      · push_neg at h
        obtain ⟨q, hq⟩ := h
        exact Or.inr ((le_iSup O q) hq)
  have hDD' : D ⊓ D' = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx'⟩
    obtain ⟨q, hq⟩ := (Opens.mem_iSup).1 hx'
    exact ((memD x).1 hx).2 q hq
  obtain ⟨W, ι, vD, hcl, hvD, hWD⟩ := closureOf P (l : Γ(P, ⊤)) D D' hDD hDD'
  refine ⟨⟨W, ι ≫ π₀, fun j i => ι ≫ c ⟨j, i⟩, ?_, ?_, ?_⟩⟩
  · intro j i
    rw [Category.assoc]
    exact congrArg (ι ≫ ·) (hc ⟨j, i⟩)
  · intro X w hu j
    refine splitOn_of_disj l Y (T j) X _ _ (fun i => ?_) hu ?_
    · rw [Category.assoc, Category.assoc]
      exact congrArg (fun k => w ≫ ι ≫ k) (hc ⟨j, i⟩)
    · intro a b hab S t ht
      by_contra hS
      obtain ⟨pt⟩ := not_isEmpty_iff.1 hS
      let q : Q := ⟨⟨j, a, b⟩, hab⟩
      have hu' : IsUnit (l : Γ(S, ⊤)) := natUnit_comp t l hu
      have key := (h3 q S (t ≫ w ≫ ι) hu').2 (by simpa [Category.assoc] using ht) pt
      have hb : ι (w (t pt)) ∈ B := by
        have := natUnit_mem (w ≫ ι) l hu (t pt)
        simpa using this
      have hD := hWD _ hb
      refine ((memD _).1 hD).2 q ?_
      simpa using key
  · intro U _ hl y z hz hsp
    let u : Spec (CommRingCat.of U) ⟶ P := WidePullback.lift y (fun i => z i.1 i.2) (fun i => hz i.1 i.2)
    have hu₀ : u ≫ π₀ = y := WidePullback.lift_base _ _ _ _
    have huc : ∀ i, u ≫ c i = z i.1 i.2 := fun i => WidePullback.lift_π _ _ _ _ _
    let a := awayPt l U
    have hau : IsUnit (l : Γ(Spec (CommRingCat.of (Localization.Away (l : U))), ⊤)) := natUnit_away l U
    have hrange : ∀ x, (a ≫ u) x ∈ D := by
      intro x
      refine (memD _).2 ⟨natUnit_mem _ l hau x, fun q hq => ?_⟩
      let V : (Spec (CommRingCat.of (Localization.Away (l : U)))).Opens := (a ≫ u) ⁻¹ᵁ O q
      have hV : ∀ v, (V.ι ≫ a ≫ u) v ∈ O q := by
        intro v
        exact v.2
      have e := (h3 q V.toScheme (V.ι ≫ a ≫ u) (natUnit_comp V.ι l hau)).1 hV
      have e' : V.ι ≫ a ≫ z q.1.1 q.1.2.1 = V.ι ≫ a ≫ z q.1.1 q.1.2.2 := by
        have e1 := huc ⟨q.1.1, q.1.2.1⟩
        have e2 := huc ⟨q.1.1, q.1.2.2⟩
        simp only [Category.assoc] at e
        rw [e1, e2] at e
        exact e
      have := disj_of_splitOn _ _ _ (hsp q.1.1) _ _ q.2 V.toScheme V.ι (by simpa [Category.assoc] using e')
      exact this.false ⟨x, hq⟩
    have hr : Set.range (a ≫ u) ⊆ Set.range D.ι := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hrange x
    let v₀ := IsOpenImmersion.lift D.ι (a ≫ u) hr
    have hv₀ : v₀ ≫ D.ι = a ≫ u := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨w, hw⟩ := liftClosed ι U (Localization.Away (l : U)) (algebraMap U _) (away_inj l U hl) u (v₀ ≫ vD)
      (by rw [Category.assoc, hvD, hv₀])
    refine ⟨w, ⟨?_, fun j i => ?_⟩, ?_⟩
    · rw [← Category.assoc, hw, hu₀]
    · rw [← Category.assoc, hw]
      exact huc ⟨j, i⟩
    · rintro w' ⟨e1, e2⟩
      rw [← cancel_mono ι, hw]
      refine WidePullback.hom_ext pi _ _ (fun i => ?_) ?_
      · have := e2 i.1 i.2
        rw [Category.assoc]
        exact this.trans (huc i).symm
      · rw [Category.assoc]
        exact e1.trans hu₀.symm

end UpperTheory.Ru.crystallineComparison
