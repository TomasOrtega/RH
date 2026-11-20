import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace DifferentiableLines.FlagIso

/- English proof (translation)
The claim follows from `GlobalTheory.hom_ext_of_fromSpecStalk fun x => @h (W.presheaf.stalk x) _ (W.toLocallyRingedSpace.isLocalRing x) (W.fromSpecStalk x)`.
-/
theorem hom_ext_local {W Z : Scheme.{0}} {a a' : W ⟶ Z}
    (h : ∀ (S : Type) [CommRing S] [IsLocalRing S] (t : Sp S ⟶ W), t ≫ a = t ≫ a') : a = a' :=
  GlobalTheory.hom_ext_of_fromSpecStalk fun x => @h (W.presheaf.stalk x) _ (W.toLocallyRingedSpace.isLocalRing x) (W.fromSpecStalk x)

/- English proof (translation)
Establish `hm : Mono (f ∣_ O)` using `⟨fun {W} a a' e => by`. Rewrite using `[← cancel_mono (f ⁻¹ᵁ O).ι]`. Use `mono W _ _ (fun w => (a w).2) ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, e, Category.assoc]⟩`. Establish `hp : IsProper (f ∣_ O)` using `IsZariskiLocalAtTarget.restrict (P := @IsProper) ‹_› O`.

Establish `: IsClosedImmersion (f ∣_ O)` using `(IsClosedImmersion.iff_isProper_and_mono _).2 ⟨hp, hm⟩`. Establish `: Surjective (f ∣_ O)` using `⟨fun z => by`. Take `⟨x, hx⟩` from `surj z.1 z.2`. Conclude with `⟨⟨x, show f x ∈ O from hx ▸ z.2⟩, Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hx)⟩⟩`. Conclude with `isIso_of_isClosedImmersion_of_surjective _`.
-/
theorem isIso_restrict {X Z : Scheme.{0}} (f : X ⟶ Z) [IsProper f] [IsReduced Z] (O : Z.Opens)
    (mono : ∀ (W : Scheme.{0}) (a a' : W ⟶ X), (∀ w, f (a w) ∈ O) → a ≫ f = a' ≫ f → a = a')
    (surj : ∀ z ∈ O, ∃ x, f x = z) : IsIso (f ∣_ O) := by
  have hm : Mono (f ∣_ O) := ⟨fun {W} a a' e => by
    rw [← cancel_mono (f ⁻¹ᵁ O).ι]
    refine mono W _ _ (fun w => (a w).2) ?_
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, e, Category.assoc]⟩
  have hp : IsProper (f ∣_ O) := IsZariskiLocalAtTarget.restrict (P := @IsProper) ‹_› O
  have : IsClosedImmersion (f ∣_ O) := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨hp, hm⟩
  have : Surjective (f ∣_ O) := ⟨fun z => by
    obtain ⟨x, hx⟩ := surj z.1 z.2
    exact ⟨⟨x, show f x ∈ O from hx ▸ z.2⟩, Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hx)⟩⟩
  exact isIso_of_isClosedImmersion_of_surjective _

/- English proof (translation)
Use `isIso_restrict f O mono surj` as an intermediate fact. Establish `hne : Nonempty O` using `hO.to_subtype`. Establish `hne' : Nonempty O.toScheme` using `hO.to_subtype`. Establish `: IsIntegral O.toScheme` using `isIntegral_of_isOpenImmersion O.ι`. Establish `h1 : IsIrreducible (Set.range (inv (f ∣_ O) ≫ (f ⁻¹ᵁ O).ι))`.

Rewrite using `[← Set.image_univ]`. Conclude with `(IrreducibleSpace.isIrreducible_univ _).image _ (Scheme.Hom.continuous _).continuousOn`. Establish `h2 : Set.range (inv (f ∣_ O) ≫ (f ⁻¹ᵁ O).ι) = ((f ⁻¹ᵁ O : X.Opens) : Set X)`. Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, (inv (f ∣_ O)).surjective.range_comp, Scheme.Opens.range_ι]`. Establish `: IrreducibleSpace X`.

Rewrite using `[irreducibleSpace_def, Set.top_eq_univ, ← dO.closure_eq, ← h2]`. Conclude with `h1.closure`. Establish `: IsIntegral X` using `isIntegral_of_irreducibleSpace_of_isReduced X`. Conclude with `GlobalTheory.isIso_of_isProper_of_quasiFinite_of_birational f GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk O hne`.
-/
theorem isIso_of_integral {X Z : Scheme.{0}} (f : X ⟶ Z) [IsProper f] [LocallyQuasiFinite f] [IsReduced X]
    [IsIntegral Z] [GlobalTheory.IsNormalScheme Z] (O : Z.Opens) (hO : (O : Set Z).Nonempty)
    (dO : Dense ((f ⁻¹ᵁ O : X.Opens) : Set X))
    (mono : ∀ (W : Scheme.{0}) (a a' : W ⟶ X), (∀ w, f (a w) ∈ O) → a ≫ f = a' ≫ f → a = a')
    (surj : ∀ z ∈ O, ∃ x, f x = z) : IsIso f := by
  have := isIso_restrict f O mono surj
  have hne : Nonempty O := hO.to_subtype
  have hne' : Nonempty O.toScheme := hO.to_subtype
  have : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion O.ι
  have h1 : IsIrreducible (Set.range (inv (f ∣_ O) ≫ (f ⁻¹ᵁ O).ι)) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (Scheme.Hom.continuous _).continuousOn
  have h2 : Set.range (inv (f ∣_ O) ≫ (f ⁻¹ᵁ O).ι) = ((f ⁻¹ᵁ O : X.Opens) : Set X) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, (inv (f ∣_ O)).surjective.range_comp, Scheme.Opens.range_ι]
  have : IrreducibleSpace X := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← dO.closure_eq, ← h2]
    exact h1.closure
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  exact GlobalTheory.isIso_of_isProper_of_quasiFinite_of_birational f GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk O hne

/- English proof (translation)
Use `GlobalTheory.IsNormalScheme.of_pred hZ` as an intermediate fact. Use `IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := MorphismProperty.isomorphisms Scheme) fun z => ?_` and prove the remaining obligations. Set `V : Z.Opens` to `GlobalTheory.IsNormalScheme.component ⟨_, irreducibleComponent_mem_irreducibleComponents z⟩`. Establish `hz : z ∈ V` using `mem_irreducibleComponent`. Use `⟨V, hz, ?_⟩` and prove the remaining obligations.

Establish `: IsIntegral V.toScheme` using `GlobalTheory.IsNormalScheme.isIntegral_component _`. Establish `: IsProper (f ∣_ V)` using `IsZariskiLocalAtTarget.restrict (P := @IsProper) ‹_› V`. Establish `: LocallyQuasiFinite (f ∣_ V)` using `MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (isPullback_morphismRestrict f V).flip ‹_›`. Use `isIso_of_integral (f ∣_ V) (V.ι ⁻¹ᵁ O) ?_ ?_ (fun W a a' ha e => ?_) fun y hy => ?_` and prove the remaining obligations. Take `⟨y, hy, hy'⟩` from `hO.inter_open_nonempty V V.isOpen ⟨z, hz⟩`.

Conclude with `⟨⟨y, hy⟩, hy'⟩`. Rewrite using `[← Scheme.Hom.comp_preimage, morphismRestrict_ι, Scheme.Hom.comp_preimage]`. Conclude with `dO.preimage (f ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap`. Rewrite using `[← cancel_mono (f ⁻¹ᵁ V).ι]`. Use `mono W _ _ (fun w => ?_) ?_` and prove the remaining obligations.

Use `ha w` as an intermediate fact. Express the relevant statement in the definitionally equal form `((f ∣_ V) (a w)).1 ∈ O at this`. Rewrite `this` using `[morphismRestrict_base_coe]`. Then use the resulting hypothesis. Rewrite using `[Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, e, Category.assoc]`. Take `⟨x, hx⟩` from `surj y.1 hy`.

Conclude with `⟨⟨x, show f x ∈ V from hx ▸ y.2⟩, Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hx)⟩`.
-/
theorem isIso_of_normal {X Z : Scheme.{0}} (f : X ⟶ Z) [IsProper f] [LocallyQuasiFinite f] [IsReduced X]
    [IsLocallyNoetherian Z] (hZ : IsNormalScheme Z) (O : Z.Opens) (hO : Dense (O : Set Z))
    (dO : Dense ((f ⁻¹ᵁ O : X.Opens) : Set X))
    (mono : ∀ (W : Scheme.{0}) (a a' : W ⟶ X), (∀ w, f (a w) ∈ O) → a ≫ f = a' ≫ f → a = a')
    (surj : ∀ z ∈ O, ∃ x, f x = z) : IsIso f := by
  have := GlobalTheory.IsNormalScheme.of_pred hZ
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := MorphismProperty.isomorphisms Scheme) fun z => ?_
  let V : Z.Opens := GlobalTheory.IsNormalScheme.component ⟨_, irreducibleComponent_mem_irreducibleComponents z⟩
  have hz : z ∈ V := mem_irreducibleComponent
  refine ⟨V, hz, ?_⟩
  have : IsIntegral V.toScheme := GlobalTheory.IsNormalScheme.isIntegral_component _
  have : IsProper (f ∣_ V) := IsZariskiLocalAtTarget.restrict (P := @IsProper) ‹_› V
  have : LocallyQuasiFinite (f ∣_ V) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (isPullback_morphismRestrict f V).flip ‹_›
  refine isIso_of_integral (f ∣_ V) (V.ι ⁻¹ᵁ O) ?_ ?_ (fun W a a' ha e => ?_) fun y hy => ?_
  · obtain ⟨y, hy, hy'⟩ := hO.inter_open_nonempty V V.isOpen ⟨z, hz⟩
    exact ⟨⟨y, hy⟩, hy'⟩
  · rw [← Scheme.Hom.comp_preimage, morphismRestrict_ι, Scheme.Hom.comp_preimage]
    exact dO.preimage (f ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap
  · rw [← cancel_mono (f ⁻¹ᵁ V).ι]
    refine mono W _ _ (fun w => ?_) ?_
    · have := ha w
      change ((f ∣_ V) (a w)).1 ∈ O at this
      rwa [morphismRestrict_base_coe] at this
    · rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, e, Category.assoc]
  · obtain ⟨x, hx⟩ := surj y.1 hy
    exact ⟨⟨x, show f x ∈ V from hx ▸ y.2⟩, Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hx)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsOpenImmersion.lift j t (by rintro _ ⟨q, rfl⟩ exact ((IsLocalRing.specializes_closedPoint q).map t.continuous).mem_open j.isOpenEmbedding.isOpen_range h), IsOpenImmersion.lift_fac _ _ _⟩`.
-/
theorem exists_fac {S : Type} [CommRing S] [IsLocalRing S] {X U : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (t : Sp S ⟶ X) (h : t (IsLocalRing.closedPoint S) ∈ Set.range j) : ∃ t' : Sp S ⟶ U, t' ≫ j = t :=
  ⟨IsOpenImmersion.lift j t (by
    rintro _ ⟨q, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint q).map t.continuous).mem_open j.isOpenEmbedding.isOpen_range h),
    IsOpenImmersion.lift_fac _ _ _⟩

/- English proof (translation)
Use `choose U j hj a hx hR using loc`. Set `𝒰 : X.OpenCover` to `Scheme.Cover.mkOfCovers X U j (fun x => ⟨x, hx x⟩) hj`. Establish `hc : ∀ x y : X, pullback.fst (j x) (j y) ≫ a x = pullback.snd _ _ ≫ a y` using `fun x y => hom_ext_local fun S _ _ t => by`. Establish `h1` using `hR x S (t ≫ pullback.fst (j x) (j y))`. Establish `h2` using `hR y S (t ≫ pullback.snd (j x) (j y))`.

Establish `e : (t ≫ pullback.snd (j x) (j y)) ≫ j y = (t ≫ pullback.fst (j x) (j y)) ≫ j x`. Rewrite using `[Category.assoc, Category.assoc]`. Conclude with `congrArg (t ≫ ·) (pullback.condition (f := j x) (g := j y)).symm`. Rewrite `h2` using `[e]`. Rewrite using `[← Category.assoc, ← Category.assoc]`.

Conclude with `uniq S _ _ _ h1 h2`. Use `⟨𝒰.glueMorphisms a hc, fun S _ _ t => ?_⟩` and prove the remaining obligations. Take `⟨x, t', rfl⟩ : ∃ (x : X) (t' : Sp S ⟶ U x), t' ≫ j x = t` from `⟨_, exists_fac (j (t (IsLocalRing.closedPoint S))) t (hx _)⟩`. Establish `e : j x ≫ 𝒰.glueMorphisms a hc = a x` using `𝒰.ι_glueMorphisms a hc x`. Rewrite using `[Category.assoc t' (j x) (𝒰.glueMorphisms a hc), e]`.

Conclude with `hR x S t'`.
-/
theorem exists_glue {X Z : Scheme.{0}}
    (R : ∀ (S : Type) [CommRing S] [IsLocalRing S], (Sp S ⟶ X) → (Sp S ⟶ Z) → Prop)
    (uniq : ∀ (S : Type) [CommRing S] [IsLocalRing S] t z z', R S t z → R S t z' → z = z')
    (loc : ∀ x : X, ∃ (U : Scheme.{0}) (j : U ⟶ X) (_ : IsOpenImmersion j) (a : U ⟶ Z), x ∈ Set.range j ∧
      ∀ (S : Type) [CommRing S] [IsLocalRing S] (t : Sp S ⟶ U), R S (t ≫ j) (t ≫ a)) :
    ∃ h : X ⟶ Z, ∀ (S : Type) [CommRing S] [IsLocalRing S] (t : Sp S ⟶ X), R S t (t ≫ h) := by
  choose U j hj a hx hR using loc
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X U j (fun x => ⟨x, hx x⟩) hj
  have hc : ∀ x y : X, pullback.fst (j x) (j y) ≫ a x = pullback.snd _ _ ≫ a y := fun x y =>
    hom_ext_local fun S _ _ t => by
      have h1 := hR x S (t ≫ pullback.fst (j x) (j y))
      have h2 := hR y S (t ≫ pullback.snd (j x) (j y))
      have e : (t ≫ pullback.snd (j x) (j y)) ≫ j y = (t ≫ pullback.fst (j x) (j y)) ≫ j x := by
        rw [Category.assoc, Category.assoc]
        exact congrArg (t ≫ ·) (pullback.condition (f := j x) (g := j y)).symm
      rw [e] at h2
      rw [← Category.assoc, ← Category.assoc]
      exact uniq S _ _ _ h1 h2
  refine ⟨𝒰.glueMorphisms a hc, fun S _ _ t => ?_⟩
  obtain ⟨x, t', rfl⟩ : ∃ (x : X) (t' : Sp S ⟶ U x), t' ≫ j x = t :=
    ⟨_, exists_fac (j (t (IsLocalRing.closedPoint S))) t (hx _)⟩
  have e : j x ≫ 𝒰.glueMorphisms a hc = a x := 𝒰.ι_glueMorphisms a hc x
  rw [Category.assoc t' (j x) (𝒰.glueMorphisms a hc), e]
  exact hR x S t'

/- English proof (translation)
Rewrite `h`, the goal using `[← basicOpen_eq_bot_iff]`. Rewrite `h` using `[Scheme.basicOpen_res]`. Assume the negation of the conclusion as `hne`. Take `⟨x, hx, hx'⟩` from `hO.inter_open_nonempty _ (X.basicOpen s).isOpen ((Opens.not_nonempty_iff_eq_bot _).not.2 hne |> not_not.1)`. Establish `: x ∈ V ⊓ O ⊓ X.basicOpen s` using `⟨⟨X.basicOpen_le s hx, hx'⟩, hx⟩`.

Rewrite `this` using `[h]`. Conclude with `this`.
-/
theorem eq_zero_of_dense {X : Scheme.{0}} [IsReduced X] {V : X.Opens} (O : X.Opens) (hO : Dense (O : Set X))
    (s : Γ(X, V)) (h : X.presheaf.map (homOfLE (inf_le_left : V ⊓ O ≤ V)).op s = 0) : s = 0 := by
  rw [← basicOpen_eq_bot_iff] at h ⊢
  rw [Scheme.basicOpen_res] at h
  by_contra hne
  obtain ⟨x, hx, hx'⟩ := hO.inter_open_nonempty _ (X.basicOpen s).isOpen
    ((Opens.not_nonempty_iff_eq_bot _).not.2 hne |> not_not.1)
  have : x ∈ V ⊓ O ⊓ X.basicOpen s := ⟨⟨X.basicOpen_le s hx, hx'⟩, hx⟩
  rw [h] at this
  exact this

end DifferentiableLines.FlagIso
