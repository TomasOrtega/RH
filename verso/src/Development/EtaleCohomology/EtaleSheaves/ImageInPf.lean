import Development.EtaleCohomology.EtaleSheaves.IsClosedImmersionOfCover

noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace LateralTheory.E.ImageInPf

/- English proof (translation)
Rewrite using `[Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]`. Introduce `U s hs`. Simplify using `only [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal] at hs`. Use `show s ∈ RingHom.ker (γ.app U).hom`. Rewrite using `[RingHom.mem_ker]`.

Apply `eq_zero_of_basicOpen_eq_bot` to reduce the goal to its premises. Rewrite using `[← Scheme.preimage_basicOpen, eq_bot_iff]`. Introduce `x hx`. It suffices to derive a contradiction. Establish `hx' : γ x ∈ Y.basicOpen s` using `hx`.

Establish `hU : γ x ∈ U.1` using `Y.basicOpen_le s hx'`. Take `⟨y, hy⟩ : γ x ∈ Set.range U.2.fromSpec` from `by rw [U.2.range_fromSpec]; exact hU`. Establish `h1` using `hs y (by show U.2.fromSpec y ∈ closure (Set.range γ)`. Rewrite using `[hy]`. Conclude with `subset_closure ⟨x, rfl⟩)`.

Establish `h2 : y ∈ U.2.fromSpec ⁻¹ᵁ Y.basicOpen s` using `by show U.2.fromSpec y ∈ Y.basicOpen s`. Rewrite using `[hy]` and apply the resulting hypothesis. Rewrite `h2` using `[U.2.fromSpec_preimage_basicOpen]`. Conclude with `h2 h1`.
-/
theorem vanishing_le_ker {V Y : Scheme.{0}} [IsReduced V] (γ : V ⟶ Y) :
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range γ)) ≤ γ.ker := by
  rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U s hs
  simp only [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal] at hs
  show s ∈ RingHom.ker (γ.app U).hom
  rw [RingHom.mem_ker]
  apply eq_zero_of_basicOpen_eq_bot
  rw [← Scheme.preimage_basicOpen, eq_bot_iff]
  intro x hx
  exfalso
  have hx' : γ x ∈ Y.basicOpen s := hx
  have hU : γ x ∈ U.1 := Y.basicOpen_le s hx'
  obtain ⟨y, hy⟩ : γ x ∈ Set.range U.2.fromSpec := by rw [U.2.range_fromSpec]; exact hU
  have h1 := hs y (by
    show U.2.fromSpec y ∈ closure (Set.range γ)
    rw [hy]; exact subset_closure ⟨x, rfl⟩)
  have h2 : y ∈ U.2.fromSpec ⁻¹ᵁ Y.basicOpen s := by
    show U.2.fromSpec y ∈ Y.basicOpen s
    rwa [hy]
  rw [U.2.fromSpec_preimage_basicOpen] at h2
  exact h2 h1

/- English proof (translation)
Use `le_antisymm (γ.ideal_ker_le U) fun s hs => vanishing_le_ker γ U ?_` and prove the remaining obligations. Simplify using `only [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]`. Introduce `y hy`. Assume the negation of the conclusion as `h`. Establish `h2 : y ∈ U.2.fromSpec ⁻¹ᵁ Y.basicOpen s`.

Rewrite using `[U.2.fromSpec_preimage_basicOpen]`. Conclude with `h`. Establish `hy' : U.2.fromSpec y ∈ closure (Set.range γ)` using `hy`. Take `⟨_, hz, x, rfl⟩` from `mem_closure_iff.mp hy' _ (Y.basicOpen s).2 h2`. Establish `h3 : x ∈ γ ⁻¹ᵁ Y.basicOpen s` using `hz`.

Rewrite `h3` using `[Scheme.preimage_basicOpen, RingHom.mem_ker.mp hs, Scheme.basicOpen_zero]`. Conclude with `h3`.
-/
theorem ker_apply_red {V Y : Scheme.{0}} [IsReduced V] (γ : V ⟶ Y) (U : Y.affineOpens) :
    γ.ker.ideal U = RingHom.ker (γ.app U).hom := by
  refine le_antisymm (γ.ideal_ker_le U) fun s hs => vanishing_le_ker γ U ?_
  simp only [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  intro y hy
  by_contra h
  have h2 : y ∈ U.2.fromSpec ⁻¹ᵁ Y.basicOpen s := by
    rw [U.2.fromSpec_preimage_basicOpen]; exact h
  have hy' : U.2.fromSpec y ∈ closure (Set.range γ) := hy
  obtain ⟨_, hz, x, rfl⟩ := mem_closure_iff.mp hy' _ (Y.basicOpen s).2 h2
  have h3 : x ∈ γ ⁻¹ᵁ Y.basicOpen s := hz
  rw [Scheme.preimage_basicOpen, RingHom.mem_ker.mp hs, Scheme.basicOpen_zero] at h3
  exact h3

/- English proof (translation)
Rewrite using `[ker_apply_red, ker_apply_red]`. Use extensionality with `x`. Simplify using `[Scheme.Hom.appLE] using! map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (V.presheaf.map (eqToHom (image_morphismRestrict_preimage γ O U)).op)).1`.
-/
theorem ker_restrict_red {V Y : Scheme.{0}} [IsReduced V] (γ : V ⟶ Y) (O : Y.Opens) (U : O.toScheme.affineOpens) :
    (γ ∣_ O).ker.ideal U = γ.ker.ideal ⟨O.ι ''ᵁ U, U.2.image_of_isOpenImmersion _⟩ := by
  rw [ker_apply_red, ker_apply_red]
  ext x
  simpa [Scheme.Hom.appLE] using! map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso (V.presheaf.map (eqToHom (image_morphismRestrict_preimage γ O U)).op)).1

/- English proof (translation)
Establish `H : t.ker ≤ (γ.imageι ∣_ O).ker`. Use `(a.le_ker_comp t).trans ?_` and prove the remaining obligations. Rewrite using `[h]`. Introduce `U`. Rewrite using `[ker_restrict_red, Scheme.ker_morphismRestrict_ideal, Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]`.

Conclude with `le_rfl`. Conclude with `⟨_, IsClosedImmersion.lift_fac t _ H⟩`.
-/
theorem image_in_red {V Y Z : Scheme.{0}} [IsReduced V] (γ : V ⟶ Y) (O : Y.Opens) (t : Z ⟶ O.toScheme)
    (a : (γ ⁻¹ᵁ O).toScheme ⟶ Z) [IsClosedImmersion t] (h : a ≫ t = γ ∣_ O) :
    ∃ b : (γ.imageι ⁻¹ᵁ O).toScheme ⟶ Z, b ≫ t = γ.imageι ∣_ O := by
  have H : t.ker ≤ (γ.imageι ∣_ O).ker := by
    refine (a.le_ker_comp t).trans ?_
    rw [h]
    intro U
    rw [ker_restrict_red, Scheme.ker_morphismRestrict_ideal, Scheme.Hom.imageι,
      Scheme.IdealSheafData.ker_subschemeι]
    exact le_rfl
  exact ⟨_, IsClosedImmersion.lift_fac t _ H⟩

/- English proof (translation)
Establish `H : t.ker ≤ (γ.imageι ∣_ O).ker`. Use `(a.le_ker_comp t).trans ?_` and prove the remaining obligations. Rewrite using `[h]`. Introduce `U`. Rewrite using `[Scheme.ker_morphismRestrict_ideal, Scheme.ker_morphismRestrict_ideal, Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]`.

Conclude with `le_rfl`. Conclude with `⟨_, IsClosedImmersion.lift_fac t _ H⟩`.
-/
theorem image_in_qc {V Y Z : Scheme.{0}} (γ : V ⟶ Y) [QuasiCompact γ] (O : Y.Opens) (t : Z ⟶ O.toScheme)
    (a : (γ ⁻¹ᵁ O).toScheme ⟶ Z) [IsClosedImmersion t] (h : a ≫ t = γ ∣_ O) :
    ∃ b : (γ.imageι ⁻¹ᵁ O).toScheme ⟶ Z, b ≫ t = γ.imageι ∣_ O := by
  have H : t.ker ≤ (γ.imageι ∣_ O).ker := by
    refine (a.le_ker_comp t).trans ?_
    rw [h]
    intro U
    rw [Scheme.ker_morphismRestrict_ideal, Scheme.ker_morphismRestrict_ideal, Scheme.Hom.imageι,
      Scheme.IdealSheafData.ker_subschemeι]
    exact le_rfl
  exact ⟨_, IsClosedImmersion.lift_fac t _ H⟩

/- English proof (translation)
Rewrite using `[Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι]`. Use `Scheme.IdealSheafData.support_antitone (vanishing_le_ker γ)` as an intermediate fact. Introduce `y hy`. Establish `h2` using `this hy`. Conclude with `h2`.
-/
theorem range_imageι_red {V Y : Scheme.{0}} [IsReduced V] (γ : V ⟶ Y) :
    Set.range γ.imageι ⊆ closure (Set.range γ) := by
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι]
  have := Scheme.IdealSheafData.support_antitone (vanishing_le_ker γ)
  intro y hy
  have h2 := this hy
  exact h2

def ImageInR : Prop := ∀ {S X₁ : Scheme.{0}} [IsReduced X₁] (p₁ : X₁ ⟶ S) [IsProper p₁]
  (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j),
    (∀ x : X₁, ∃ j, x ∈ U j) → (∀ j, IsSeparated (qj j)) →
    (∀ j, IsClosedImmersion (e j)) → (∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) → (∀ j, π j ≫ qj j = q) →
    ∀ (V : X₁.Opens), IsAffineOpen V → ∀ (hV : ∀ j, V ≤ U j) (γ : V.toScheme ⟶ pullback p₁ q),
      γ ≫ pullback.fst p₁ q = V.ι → (∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) →
      ∀ j,
      ∀ (Z : Scheme.{0}) (t : Z ⟶ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j)).toScheme) (a : (γ ⁻¹ᵁ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))).toScheme ⟶ Z),
        IsClosedImmersion t → a ≫ t = γ ∣_ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j)) →
        ∃ b : (γ.imageι ⁻¹ᵁ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))).toScheme ⟶ Z, b ≫ t = γ.imageι ∣_ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))

/- English proof (translation)
Introduce `S X₁ _ p₁ _ n U Pj qj W e P q π _ _ _ _ _ V _ hV γ _ _ j Z t a ht hat`. Conclude with `image_in_red γ _ t a hat`.
-/
theorem ImageInR_of : ImageInR := by
  intro S X₁ _ p₁ _ n U Pj qj W e P q π _ _ _ _ _ V _ hV γ _ _ j Z t a ht hat
  exact image_in_red γ _ t a hat

/- English proof (translation)
Introduce and unpack `_ ⟨y, rfl⟩`. Establish `hz : γ.imageι y ∈ closure (Set.range γ)` using `range_imageι_red γ ⟨y, rfl⟩`. Take `⟨j, hj⟩` from `hcov (pullback.fst p₁ q (γ.imageι y))`. Use `Set.mem_iUnion.mpr ⟨j, ?_⟩` and prove the remaining obligations. Use `set z := γ.imageι y`.

Set `O : (pullback p₁ q).Opens` to `pullback.fst p₁ q ⁻¹ᵁ U j`. Establish `hcomm : ((pullback.fst p₁ q ∣_ U j) ≫ e j ≫ (W j).ι) ≫ qj j = (O.ι ≫ pullback.snd p₁ q ≫ π j) ≫ qj j`. Simplify using `only [Category.assoc, hc j, hπ j, morphismRestrict_ι_assoc, pullback.condition]`. Both sides reduce to the same expression. Set `f : O.toScheme ⟶ pullback (qj j) (qj j)` to `pullback.lift _ _ hcomm`.

Establish `hD : IsClosed (Set.range (pullback.diagonal (qj j)))` using `(pullback.diagonal (qj j)).isClosedEmbedding.isClosed_range`. Establish `hrange : Set.range γ ⊆ Set.range O.ι`. Introduce and unpack `_ ⟨v, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Use `show pullback.fst p₁ q (γ v) ∈ U j`.

Rewrite using `[← Scheme.Hom.comp_apply, hγ1]`. Conclude with `hV j v.2`. Set `γO : V.toScheme ⟶ O.toScheme` to `IsOpenImmersion.lift O.ι γ hrange`. Establish `hγO : γO ≫ O.ι = γ` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hfac : γO ≫ f = (X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) ≫ pullback.diagonal (qj j)`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [f, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]`. Establish `h1 : γO ≫ (pullback.fst p₁ q ∣_ U j) = X₁.homOfLE (hV j)`. Rewrite using `[← cancel_mono (U j).ι, Category.assoc, morphismRestrict_ι, reassoc_of% hγO, hγ1, Scheme.homOfLE_ι]`. Rewrite using `[reassoc_of% h1]`.

Simplify using `only [f, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]`. Rewrite using `[← hγ2 j, ← hγO, Category.assoc]`. Take `⟨zO, hzO⟩ : z ∈ Set.range O.ι` from `by rw [Scheme.Opens.range_ι]; exact hj`. Establish `hcl : zO ∈ closure (O.ι ⁻¹' Set.range γ)`. Rewrite using `[← O.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage O.ι.continuous]`.

Use `show O.ι zO ∈ closure (Set.range γ)`. Rewrite using `[hzO]`. Conclude with `hz`. Establish `hsub : O.ι ⁻¹' Set.range γ ⊆ f ⁻¹' Set.range (pullback.diagonal (qj j))`. Introduce and unpack `w ⟨v, hv⟩`.

Establish `hw : w = γO v` using `O.ι.isOpenEmbedding.injective (by`. Rewrite using `[← Scheme.Hom.comp_apply, hγO, hv])`. Use `⟨(X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) v, ?_⟩` and prove the remaining obligations. Rewrite using `[hw, ← Scheme.Hom.comp_apply, ← hfac, Scheme.Hom.comp_apply]`. Take `⟨p, hp⟩` from `closure_minimal hsub (hD.preimage f.continuous) hcl`.

Establish `e1 : (f ≫ pullback.fst _ _) zO = p`. Rewrite using `[Scheme.Hom.comp_apply, ← hp, ← Scheme.Hom.comp_apply, pullback.diagonal_fst]`. Both sides reduce to the same expression. Establish `e2 : (f ≫ pullback.snd _ _) zO = p`. Rewrite using `[Scheme.Hom.comp_apply, ← hp, ← Scheme.Hom.comp_apply, pullback.diagonal_snd]`.

Both sides reduce to the same expression. Simplify using `only [f, pullback.lift_fst, pullback.lift_snd] at e1 e2`. Use `show π j (pullback.snd p₁ q z) ∈ W j`. Establish `: π j (pullback.snd p₁ q z) = p`. Rewrite using `[← e2, ← hzO]`.

Simplify using `only [Scheme.Hom.comp_apply]`. Rewrite using `[this, ← e1]`. Simplify using `only [Scheme.Hom.comp_apply]`. Establish `hmem : ∀ a : (W j).toScheme, (W j).ι a ∈ W j` using `fun a => by`. Conclude with `(Scheme.Opens.range_ι (W j)).le ⟨a, rfl⟩`.

Conclude with `hmem _`.
-/
theorem covered_red {S X₁ : Scheme.{0}} [IsReduced X₁] (p₁ : X₁ ⟶ S)
  (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j)
    (hcov : ∀ x : X₁, ∃ j, x ∈ U j) (hsep : ∀ j, IsSeparated (qj j))
    (hc : ∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) (hπ : ∀ j, π j ≫ qj j = q)
    (V : X₁.Opens) (hV : ∀ j, V ≤ U j) (γ : V.toScheme ⟶ pullback p₁ q)
    (hγ1 : γ ≫ pullback.fst p₁ q = V.ι)
    (hγ2 : ∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) :
      Set.range (γ.imageι ≫ pullback.snd p₁ q) ⊆ ⋃ j, ((π j ⁻¹ᵁ W j : P.Opens) : Set P) := by
  rintro _ ⟨y, rfl⟩
  have hz : γ.imageι y ∈ closure (Set.range γ) := range_imageι_red γ ⟨y, rfl⟩
  obtain ⟨j, hj⟩ := hcov (pullback.fst p₁ q (γ.imageι y))
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  set z := γ.imageι y
  let O : (pullback p₁ q).Opens := pullback.fst p₁ q ⁻¹ᵁ U j
  have hcomm : ((pullback.fst p₁ q ∣_ U j) ≫ e j ≫ (W j).ι) ≫ qj j = (O.ι ≫ pullback.snd p₁ q ≫ π j) ≫ qj j := by
    simp only [Category.assoc, hc j, hπ j, morphismRestrict_ι_assoc, pullback.condition]
    rfl
  let f : O.toScheme ⟶ pullback (qj j) (qj j) := pullback.lift _ _ hcomm
  have hD : IsClosed (Set.range (pullback.diagonal (qj j))) :=
    (pullback.diagonal (qj j)).isClosedEmbedding.isClosed_range
  have hrange : Set.range γ ⊆ Set.range O.ι := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι]
    show pullback.fst p₁ q (γ v) ∈ U j
    rw [← Scheme.Hom.comp_apply, hγ1]
    exact hV j v.2
  let γO : V.toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι γ hrange
  have hγO : γO ≫ O.ι = γ := IsOpenImmersion.lift_fac _ _ _
  have hfac : γO ≫ f = (X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) ≫ pullback.diagonal (qj j) := by
    apply pullback.hom_ext
    · simp only [f, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      have h1 : γO ≫ (pullback.fst p₁ q ∣_ U j) = X₁.homOfLE (hV j) := by
        rw [← cancel_mono (U j).ι, Category.assoc, morphismRestrict_ι, reassoc_of% hγO, hγ1,
          Scheme.homOfLE_ι]
      rw [reassoc_of% h1]
    · simp only [f, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
      rw [← hγ2 j, ← hγO, Category.assoc]
  obtain ⟨zO, hzO⟩ : z ∈ Set.range O.ι := by rw [Scheme.Opens.range_ι]; exact hj
  have hcl : zO ∈ closure (O.ι ⁻¹' Set.range γ) := by
    rw [← O.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage O.ι.continuous]
    show O.ι zO ∈ closure (Set.range γ)
    rw [hzO]; exact hz
  have hsub : O.ι ⁻¹' Set.range γ ⊆ f ⁻¹' Set.range (pullback.diagonal (qj j)) := by
    rintro w ⟨v, hv⟩
    have hw : w = γO v := O.ι.isOpenEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, hγO, hv])
    refine ⟨(X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) v, ?_⟩
    rw [hw, ← Scheme.Hom.comp_apply, ← hfac, Scheme.Hom.comp_apply]
  obtain ⟨p, hp⟩ := closure_minimal hsub (hD.preimage f.continuous) hcl
  have e1 : (f ≫ pullback.fst _ _) zO = p := by
    rw [Scheme.Hom.comp_apply, ← hp, ← Scheme.Hom.comp_apply, pullback.diagonal_fst]; rfl
  have e2 : (f ≫ pullback.snd _ _) zO = p := by
    rw [Scheme.Hom.comp_apply, ← hp, ← Scheme.Hom.comp_apply, pullback.diagonal_snd]; rfl
  simp only [f, pullback.lift_fst, pullback.lift_snd] at e1 e2
  show π j (pullback.snd p₁ q z) ∈ W j
  have : π j (pullback.snd p₁ q z) = p := by
    rw [← e2, ← hzO]; simp only [Scheme.Hom.comp_apply]
  rw [this, ← e1]
  simp only [Scheme.Hom.comp_apply]
  have hmem : ∀ a : (W j).toScheme, (W j).ι a ∈ W j := fun a => by
    exact (Scheme.Opens.range_ι (W j)).le ⟨a, rfl⟩
  exact hmem _

def GraphT : Prop := ∀ {S X₁ : Scheme.{0}} (p₁ : X₁ ⟶ S) [IsProper p₁]
  (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j),
    (∀ x : X₁, ∃ j, x ∈ U j) → (∀ j, IsSeparated (qj j)) →
    (∀ j, IsClosedImmersion (e j)) → (∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) → (∀ j, π j ≫ qj j = q) →
    ∀ (V : X₁.Opens), IsAffineOpen V → ∀ (hV : ∀ j, V ≤ U j) (γ : V.toScheme ⟶ pullback p₁ q),
      γ ≫ pullback.fst p₁ q = V.ι → (∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) →
      ∀ j,
      ∃ (Z : Scheme.{0}) (t : Z ⟶ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j)).toScheme) (a : (γ ⁻¹ᵁ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))).toScheme ⟶ Z),
        IsClosedImmersion t ∧ IsClosedImmersion (t ≫ pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j)) ∧
        a ≫ t = γ ∣_ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))

/- English proof (translation)
Introduce `S X₁ p₁ _ n U Pj qj W e P q π _ _ he hc hπ V _ hV γ h1 h2 j`. Use `he j` as an intermediate fact. Set `z1` to `pullback.fst (π j ∣_ W j) (e j)`. Set `z2` to `pullback.snd (π j ∣_ W j) (e j)`. Establish `hz : z1 ≫ (π j ∣_ W j) = z2 ≫ e j` using `pullback.condition`.

Establish `hw : (z2 ≫ (U j).ι) ≫ p₁ = (z1 ≫ (π j ⁻¹ᵁ W j).ι) ≫ q`. Rewrite using `[Category.assoc, ← hc j, ← reassoc_of% hz, morphismRestrict_ι_assoc, hπ j, Category.assoc]`. Set `t0` to `pullback.lift _ _ hw`. Establish `hP` using `isPullback_morphismRestrict (pullback.snd p₁ q) (π j ⁻¹ᵁ W j)`. Establish `ht0 : z1 ≫ (π j ⁻¹ᵁ W j).ι = t0 ≫ pullback.snd p₁ q` using `(pullback.lift_snd _ _ _).symm`.

Establish `ht0' : t0 ≫ pullback.fst p₁ q = z2 ≫ (U j).ι` using `pullback.lift_fst _ _ _`. Set `t` to `hP.lift z1 t0 ht0`. Establish `e1 : t ≫ pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j) = z1` using `hP.lift_fst _ _ _`. Establish `e2 : t ≫ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j)).ι = t0` using `hP.lift_snd _ _ _`. Establish `hcl : IsClosedImmersion (t ≫ pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j))` using `by rw [e1]; infer_instance`.

Establish `ha : (γ ∣_ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j)) ≫ pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j)) ≫ (π j ∣_ W j) = ((γ ⁻¹ᵁ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))).ι ≫ X₁.homOfLE (hV j)) ≫ e j`. Rewrite using `[← cancel_mono (W j).ι]`. Simplify using `only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, h2 j]`. Set `a` to `pullback.lift _ _ ha`. Establish `a1 : a ≫ z1 = _` using `pullback.lift_fst _ _ _`.

Establish `a2 : a ≫ z2 = _` using `pullback.lift_snd _ _ _`. Use `⟨_, t, a, IsClosedImmersion.of_comp t (pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j)), hcl, ?_⟩` and prove the remaining obligations. Apply `hP.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, e1, a1]`. Rewrite using `[Category.assoc, e2, morphismRestrict_ι]`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, ht0', reassoc_of% a2, Scheme.homOfLE_ι, Category.assoc, h1]`. Rewrite using `[Category.assoc, ← ht0, reassoc_of% a1, morphismRestrict_ι, morphismRestrict_ι_assoc, Category.assoc]`.
-/
theorem GraphT_of : GraphT := by
  intro S X₁ p₁ _ n U Pj qj W e P q π _ _ he hc hπ V _ hV γ h1 h2 j
  have := he j
  let z1 := pullback.fst (π j ∣_ W j) (e j)
  let z2 := pullback.snd (π j ∣_ W j) (e j)
  have hz : z1 ≫ (π j ∣_ W j) = z2 ≫ e j := pullback.condition
  have hw : (z2 ≫ (U j).ι) ≫ p₁ = (z1 ≫ (π j ⁻¹ᵁ W j).ι) ≫ q := by
    rw [Category.assoc, ← hc j, ← reassoc_of% hz, morphismRestrict_ι_assoc, hπ j, Category.assoc]
  let t0 := pullback.lift _ _ hw
  have hP := isPullback_morphismRestrict (pullback.snd p₁ q) (π j ⁻¹ᵁ W j)
  have ht0 : z1 ≫ (π j ⁻¹ᵁ W j).ι = t0 ≫ pullback.snd p₁ q := (pullback.lift_snd _ _ _).symm
  have ht0' : t0 ≫ pullback.fst p₁ q = z2 ≫ (U j).ι := pullback.lift_fst _ _ _
  let t := hP.lift z1 t0 ht0
  have e1 : t ≫ pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j) = z1 := hP.lift_fst _ _ _
  have e2 : t ≫ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j)).ι = t0 := hP.lift_snd _ _ _
  have hcl : IsClosedImmersion (t ≫ pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j)) := by rw [e1]; infer_instance
  have ha : (γ ∣_ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j)) ≫ pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j)) ≫ (π j ∣_ W j) =
      ((γ ⁻¹ᵁ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))).ι ≫ X₁.homOfLE (hV j)) ≫ e j := by
    rw [← cancel_mono (W j).ι]
    simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, h2 j]
  let a := pullback.lift _ _ ha
  have a1 : a ≫ z1 = _ := pullback.lift_fst _ _ _
  have a2 : a ≫ z2 = _ := pullback.lift_snd _ _ _
  refine ⟨_, t, a, IsClosedImmersion.of_comp t (pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j)), hcl, ?_⟩
  apply hP.hom_ext
  · rw [Category.assoc, e1, a1]
  · rw [Category.assoc, e2, morphismRestrict_ι]
    apply pullback.hom_ext
    · rw [Category.assoc, ht0', reassoc_of% a2, Scheme.homOfLE_ι, Category.assoc, h1]
    · rw [Category.assoc, ← ht0, reassoc_of% a1, morphismRestrict_ι, morphismRestrict_ι_assoc, Category.assoc]

/- English proof (translation)
Introduce `S X₁ p₁ _ hX n U Pj qj W e P q π hUn hUc hsep he hc hπ hUP`. Take `⟨x₀⟩ : Nonempty X₁` from `inferInstance`. Take `⟨j₀, -⟩` from `hUc x₀`. Set `V₀ : X₁.Opens` to `Finset.univ.inf U`. Establish `hV₀ : ∀ j, V₀ ≤ U j` using `fun j => Finset.inf_le (Finset.mem_univ j)`.

Take `⟨x, hx⟩` from `LateralTheory.E.CorePf.inf_nonempty U hUn _ ⟨j₀, Finset.mem_univ _⟩`. Take `⟨V', hVa, hxV, hVle⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp X₁.isBasis_affineOpens (U := V₀) hx`. Take `⟨V, rfl⟩ : ∃ V : X₁.Opens, V = V'` from `⟨V', rfl⟩`. Use `replace hVa : IsAffineOpen V := hVa`. Establish `hV : ∀ j, (V : X₁.Opens) ≤ U j` using `fun j => hVle.trans (hV₀ j)`.

Take `⟨g, ⟨hg1, hg2⟩, -⟩` from `hUP ((V : X₁.Opens).ι ≫ p₁) (fun j => X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) (by`. Introduce `j`. Simplify using `only [Category.assoc, hc j, Scheme.homOfLE_ι_assoc])`. Set `γ : (V : X₁.Opens).toScheme ⟶ pullback p₁ q` to `pullback.lift (V : X₁.Opens).ι g hg1.symm`. Establish `hγ1 : γ ≫ pullback.fst p₁ q = (V : X₁.Opens).ι` using `pullback.lift_fst _ _ _`.

Establish `hγ2 : ∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι`. Introduce `j`. Rewrite using `[pullback.lift_snd_assoc, hg2 j]`. Use `⟨γ.image, γ.imageι, V, γ.toImage, inferInstance, LateralTheory.E.CorePf2.isClosedImmersion_of_cover _ (fun j => π j ⁻¹ᵁ W j) (LateralTheory.E.CorePf2.range_closed p₁ q γ) (covered_red p₁ n U Pj qj W e P q π hUc hsep hc hπ V hV γ hγ1 hγ2) (fun j => ?_), ⟨x, hxV⟩, ?_⟩` and prove the remaining obligations. Take `⟨Z, t, a, ht, hts, hat⟩` from `GraphT_of p₁ n U Pj qj W e P q π hUc hsep he hc hπ V hVa hV γ hγ1 hγ2 j`.

Take `⟨b, hb⟩` from `image_in_red γ _ t a hat`. Rewrite using `[morphismRestrict_comp, ← hb, Category.assoc]`. Establish `: IsClosedImmersion (b ≫ t)` using `by rw [hb]; infer_instance`. Establish `: IsClosedImmersion b` using `IsClosedImmersion.of_comp_isClosedImmersion b t`. Conclude with `@IsClosedImmersion.comp _ _ _ b _ this hts`.

Rewrite using `[Scheme.Hom.toImage_imageι_assoc, hγ1]`.
-/
theorem Core_of : LateralTheory.E.ChowGraphCut.Core := by
  intro S X₁ p₁ _ hX n U Pj qj W e P q π hUn hUc hsep he hc hπ hUP
  obtain ⟨x₀⟩ : Nonempty X₁ := inferInstance
  obtain ⟨j₀, -⟩ := hUc x₀
  let V₀ : X₁.Opens := Finset.univ.inf U
  have hV₀ : ∀ j, V₀ ≤ U j := fun j => Finset.inf_le (Finset.mem_univ j)
  obtain ⟨x, hx⟩ := LateralTheory.E.CorePf.inf_nonempty U hUn _ ⟨j₀, Finset.mem_univ _⟩
  obtain ⟨V', hVa, hxV, hVle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X₁.isBasis_affineOpens (U := V₀) hx
  obtain ⟨V, rfl⟩ : ∃ V : X₁.Opens, V = V' := ⟨V', rfl⟩
  replace hVa : IsAffineOpen V := hVa
  have hV : ∀ j, (V : X₁.Opens) ≤ U j := fun j => hVle.trans (hV₀ j)
  obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := hUP ((V : X₁.Opens).ι ≫ p₁) (fun j => X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) (by
    intro j
    simp only [Category.assoc, hc j, Scheme.homOfLE_ι_assoc])
  let γ : (V : X₁.Opens).toScheme ⟶ pullback p₁ q := pullback.lift (V : X₁.Opens).ι g hg1.symm
  have hγ1 : γ ≫ pullback.fst p₁ q = (V : X₁.Opens).ι := pullback.lift_fst _ _ _
  have hγ2 : ∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι := by
    intro j; rw [pullback.lift_snd_assoc, hg2 j]
  refine ⟨γ.image, γ.imageι, V, γ.toImage, inferInstance,
    LateralTheory.E.CorePf2.isClosedImmersion_of_cover _ (fun j => π j ⁻¹ᵁ W j) (LateralTheory.E.CorePf2.range_closed p₁ q γ)
      (covered_red p₁ n U Pj qj W e P q π hUc hsep hc hπ V hV γ hγ1 hγ2)
      (fun j => ?_), ⟨x, hxV⟩, ?_⟩
  · obtain ⟨Z, t, a, ht, hts, hat⟩ := GraphT_of p₁ n U Pj qj W e P q π hUc hsep he hc hπ V hVa hV γ hγ1 hγ2 j
    obtain ⟨b, hb⟩ := image_in_red γ _ t a hat
    rw [morphismRestrict_comp, ← hb, Category.assoc]
    have : IsClosedImmersion (b ≫ t) := by rw [hb]; infer_instance
    have : IsClosedImmersion b := IsClosedImmersion.of_comp_isClosedImmersion b t
    exact @IsClosedImmersion.comp _ _ _ b _ this hts
  · rw [Scheme.Hom.toImage_imageι_assoc, hγ1]

end LateralTheory.E.ImageInPf
