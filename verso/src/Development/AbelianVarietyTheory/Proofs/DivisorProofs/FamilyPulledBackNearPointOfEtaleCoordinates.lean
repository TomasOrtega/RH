import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.EtalePull

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, rfl⟩`. Establish `: s = t` using `Subsingleton.elim (α := PrimeSpectrum Ω) s t`. Simplify using `[this]`.

Introduce and unpack `rfl`. Conclude with `⟨t, rfl⟩`.
-/
theorem range_pt {Ω : Type} [Field Ω] {X : Scheme.{0}} (p : Sp Ω ⟶ X) (t : Sp Ω) : Set.range p = {p t} := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    have : s = t := Subsingleton.elim (α := PrimeSpectrum Ω) s t
    simp [this]
  · rintro rfl
    exact ⟨t, rfl⟩

/- English proof (translation)
Rewrite using `[← Set.range_comp]`. Conclude with `congrArg Set.range (funext fun t => Scheme.Hom.comp_apply f g t)`.
-/
theorem range_comp' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) : Set.range (f ≫ g) = g '' Set.range f := by
  rw [← Set.range_comp]
  exact congrArg Set.range (funext fun t => Scheme.Hom.comp_apply f g t)

/- English proof (translation)
Establish `hΔ : IsOpenImmersion (pullback.diagonal f)` using `inferInstance`. Set `r : pullback f f ⟶ U` to `pullback.fst f f ≫ f ≫ q`. Establish `h1 : IsClosed (r '' (Set.range (pullback.diagonal f))ᶜ)` using `r.isClosedMap _ (pullback.diagonal f).isOpenEmbedding.isOpen_range.isClosed_compl`. Establish `h2 : IsClosed (q '' (Set.range f)ᶜ)` using `q.isClosedMap _ f.isOpenMap.isOpen_range.isClosed_compl`. Set `W : U.Opens` to `⟨(r '' (Set.range (pullback.diagonal f))ᶜ)ᶜ ∩ (q '' (Set.range f)ᶜ)ᶜ, h1.isOpen_compl.inter h2.isOpen_compl⟩`.

Use `⟨W, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨z, hz, hzx⟩`. Apply `hz` to reduce the goal to its premises. Set `w` to `(pullback f f).fromSpecResidueField z`. Establish `hw : w ≫ pullback.fst f f = w ≫ pullback.snd f f`.

Use `hinj ((pullback f f).residueField z) _ _ ?_ ?_` and prove the remaining obligations. Establish `: Set.range (w ≫ r) = {x}`. Rewrite using `[range_comp', Scheme.range_fromSpecResidueField, Set.image_singleton, hzx]`. Establish `e : (w ≫ pullback.fst f f) ≫ f ≫ q = w ≫ r` using `Category.assoc _ _ _`. Conclude with `(congrArg (fun k : Spec ((pullback f f).residueField z) ⟶ U => Set.range k) e).trans this`.

Simplify using `[pullback.condition]`. Establish `hw2 : w = (w ≫ pullback.fst f f) ≫ pullback.diagonal f`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Simplify using `[hw]`.

Establish `: z ∈ Set.range w` using `by rw [Scheme.range_fromSpecResidueField]; rfl`. Take `⟨t, ht⟩` from `this`. Use `⟨(w ≫ pullback.fst f f) t, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← hw2, ht]`. Introduce and unpack `⟨y, hy, hyx⟩`.

Conclude with `hy (hsurj y hyx)`. Establish `hm : Mono (f ∣_ (q ⁻¹ᵁ W))`. Use `⟨fun {T} u v huv => ?_⟩` and prove the remaining obligations. Establish `e : (u ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι) ≫ f = (v ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι) ≫ f`. Simplify using `only [Category.assoc, ← morphismRestrict_ι]`.

Rewrite using `[← Category.assoc, huv, Category.assoc]`. Set `w : T ⟶ pullback f f` to `pullback.lift _ _ e`. Establish `hr : Set.range w ⊆ Set.range (pullback.diagonal f)`. Introduce and unpack `_ ⟨t, rfl⟩`. Assume the negation of the conclusion as `hn`.

Establish `hW : q (f ((f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι (u t))) ∈ W` using `(u t).2`. Use `hW.1 ⟨w t, hn, ?_⟩` and prove the remaining obligations. Establish `e3 : w ≫ r = u ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι ≫ f ≫ q`. Simplify using `only [w, r, pullback.lift_fst_assoc, Category.assoc]`. Rewrite using `[← Scheme.Hom.comp_apply, e3]`.

Simplify using `only [Scheme.Hom.comp_apply]`. Establish `hl` using `IsOpenImmersion.lift_fac (pullback.diagonal f) w hr`. Establish `e1` using `congrArg (· ≫ pullback.fst f f) hl`. Establish `e2` using `congrArg (· ≫ pullback.snd f f) hl`. Simplify using `only [w, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id, pullback.lift_fst, pullback.lift_snd] at e1 e2`.

Rewrite using `[← cancel_mono (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι, ← e1, e2]`. Establish `ho : IsOpenImmersion (f ∣_ (q ⁻¹ᵁ W))` using `IsOpenImmersion.of_flat_of_mono _`. Use `(isIso_iff_isOpenImmersion_and_surjective _).2 ⟨ho, ⟨fun y => ?_⟩⟩` and prove the remaining obligations. Establish `hW : q y.1 ∈ W` using `y.2`. Establish `: y.1 ∈ Set.range f`.

Assume the negation of the conclusion as `hn`. Conclude with `hW.2 ⟨y.1, hn, rfl⟩`. Take `⟨s, hs⟩` from `this`. Use `⟨⟨s, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show q (f s) ∈ W`.

Rewrite using `[hs]`. Conclude with `hW`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(morphismRestrict_base_coe _ _ _).trans hs`.
-/
theorem exists_isIso_restrict {X Y U : Scheme.{0}} (f : X ⟶ Y) (q : Y ⟶ U) [Etale f] [UniversallyClosed f]
    [UniversallyClosed q] (x : U)
    (hinj : ∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ f ≫ q) = {x} → p ≫ f = p' ≫ f → p = p')
    (hsurj : ∀ y : Y, q y = x → y ∈ Set.range f) :
    ∃ W : U.Opens, x ∈ W ∧ IsIso (f ∣_ (q ⁻¹ᵁ W)) := by
  have hΔ : IsOpenImmersion (pullback.diagonal f) := inferInstance
  let r : pullback f f ⟶ U := pullback.fst f f ≫ f ≫ q
  have h1 : IsClosed (r '' (Set.range (pullback.diagonal f))ᶜ) :=
    r.isClosedMap _ (pullback.diagonal f).isOpenEmbedding.isOpen_range.isClosed_compl
  have h2 : IsClosed (q '' (Set.range f)ᶜ) :=
    q.isClosedMap _ f.isOpenMap.isOpen_range.isClosed_compl
  let W : U.Opens := ⟨(r '' (Set.range (pullback.diagonal f))ᶜ)ᶜ ∩ (q '' (Set.range f)ᶜ)ᶜ,
    h1.isOpen_compl.inter h2.isOpen_compl⟩
  refine ⟨W, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨z, hz, hzx⟩
    apply hz
    let w := (pullback f f).fromSpecResidueField z
    have hw : w ≫ pullback.fst f f = w ≫ pullback.snd f f := by
      refine hinj ((pullback f f).residueField z) _ _ ?_ ?_
      · have : Set.range (w ≫ r) = {x} := by
          rw [range_comp', Scheme.range_fromSpecResidueField, Set.image_singleton, hzx]
        have e : (w ≫ pullback.fst f f) ≫ f ≫ q = w ≫ r := Category.assoc _ _ _
        exact (congrArg (fun k : Spec ((pullback f f).residueField z) ⟶ U => Set.range k) e).trans this
      · simp [pullback.condition]
    have hw2 : w = (w ≫ pullback.fst f f) ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp
      · simp [hw]
    have : z ∈ Set.range w := by rw [Scheme.range_fromSpecResidueField]; rfl
    obtain ⟨t, ht⟩ := this
    refine ⟨(w ≫ pullback.fst f f) t, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hw2, ht]
  · rintro ⟨y, hy, hyx⟩
    exact hy (hsurj y hyx)
  · have hm : Mono (f ∣_ (q ⁻¹ᵁ W)) := by
      refine ⟨fun {T} u v huv => ?_⟩
      have e : (u ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι) ≫ f = (v ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι) ≫ f := by
        simp only [Category.assoc, ← morphismRestrict_ι]
        rw [← Category.assoc, huv, Category.assoc]
      let w : T ⟶ pullback f f := pullback.lift _ _ e
      have hr : Set.range w ⊆ Set.range (pullback.diagonal f) := by
        rintro _ ⟨t, rfl⟩
        by_contra hn
        have hW : q (f ((f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι (u t))) ∈ W := (u t).2
        refine hW.1 ⟨w t, hn, ?_⟩
        have e3 : w ≫ r = u ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι ≫ f ≫ q := by
          simp only [w, r, pullback.lift_fst_assoc, Category.assoc]
        rw [← Scheme.Hom.comp_apply, e3]
        simp only [Scheme.Hom.comp_apply]
      have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) w hr
      have e1 := congrArg (· ≫ pullback.fst f f) hl
      have e2 := congrArg (· ≫ pullback.snd f f) hl
      simp only [w, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
        pullback.lift_fst, pullback.lift_snd] at e1 e2
      rw [← cancel_mono (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι, ← e1, e2]
    have ho : IsOpenImmersion (f ∣_ (q ⁻¹ᵁ W)) := IsOpenImmersion.of_flat_of_mono _
    refine (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨ho, ⟨fun y => ?_⟩⟩
    have hW : q y.1 ∈ W := y.2
    have : y.1 ∈ Set.range f := by
      by_contra hn
      exact hW.2 ⟨y.1, hn, rfl⟩
    obtain ⟨s, hs⟩ := this
    refine ⟨⟨s, ?_⟩, ?_⟩
    · show q (f s) ∈ W
      rw [hs]; exact hW
    · apply Subtype.ext
      exact (morphismRestrict_base_coe _ _ _).trans hs

/- English proof (translation)
Take `⟨W, hW, hiso⟩` from `exists_isIso_restrict (f ∣_ (q ⁻¹ᵁ V)) (q ∣_ V) ⟨x, hx⟩ (by`. Introduce `Ω _ p p' h1 h2`. Rewrite using `[← cancel_mono (f ⁻¹ᵁ (q ⁻¹ᵁ V)).ι]`. Apply `hinj` to reduce the goal to its premises. Establish `e : (p ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ V)).ι) ≫ f ≫ q = (p ≫ f ∣_ (q ⁻¹ᵁ V) ≫ q ∣_ V) ≫ V.ι`.

Simplify using the standard rewrite rules. Rewrite using `[e, range_comp', h1]`. Conclude with `Set.image_singleton`. Simplify using `only [Category.assoc, ← morphismRestrict_ι]`. Rewrite using `[← Category.assoc, h2, Category.assoc]) (by`.

Introduce `y hy`. Establish `h1 : q y.1 = x` using `(morphismRestrict_base_coe q V y).symm.trans (congrArg Subtype.val hy)`. Take `⟨s, hs⟩` from `hsurj y.1 h1`. Use `⟨⟨s, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show q (f s) ∈ V`.

Rewrite using `[hs, h1]`. Conclude with `hx`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(morphismRestrict_base_coe _ _ _).trans hs)`. Use `⟨V.ι ''ᵁ W, ⟨⟨x, hx⟩, hW, rfl⟩, V.ι_image_le W, ?_⟩` and prove the remaining obligations.

Rewrite using `[← image_morphismRestrict_preimage]`. Conclude with `(MorphismProperty.arrow_mk_iso_iff (.isomorphisms Scheme) (morphismRestrictRestrict f (q ⁻¹ᵁ V) ((q ∣_ V) ⁻¹ᵁ W))).1 hiso`.
-/
theorem exists_isIso_restrict' {X Y U : Scheme.{0}} (f : X ⟶ Y) (q : Y ⟶ U) [UniversallyClosed f]
    [UniversallyClosed q] (x : U) (V : U.Opens) (hx : x ∈ V) [Etale (f ∣_ (q ⁻¹ᵁ V))]
    (hinj : ∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ f ≫ q) = {x} → p ≫ f = p' ≫ f → p = p')
    (hsurj : ∀ y : Y, q y = x → y ∈ Set.range f) :
    ∃ W : U.Opens, x ∈ W ∧ W ≤ V ∧ IsIso (f ∣_ (q ⁻¹ᵁ W)) := by
  obtain ⟨W, hW, hiso⟩ := exists_isIso_restrict (f ∣_ (q ⁻¹ᵁ V)) (q ∣_ V) ⟨x, hx⟩ (by
    intro Ω _ p p' h1 h2
    rw [← cancel_mono (f ⁻¹ᵁ (q ⁻¹ᵁ V)).ι]
    apply hinj
    · have e : (p ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ V)).ι) ≫ f ≫ q = (p ≫ f ∣_ (q ⁻¹ᵁ V) ≫ q ∣_ V) ≫ V.ι := by
        simp
      rw [e, range_comp', h1]
      exact Set.image_singleton
    · simp only [Category.assoc, ← morphismRestrict_ι]
      rw [← Category.assoc, h2, Category.assoc]) (by
    intro y hy
    have h1 : q y.1 = x := (morphismRestrict_base_coe q V y).symm.trans (congrArg Subtype.val hy)
    obtain ⟨s, hs⟩ := hsurj y.1 h1
    refine ⟨⟨s, ?_⟩, ?_⟩
    · show q (f s) ∈ V
      rw [hs, h1]; exact hx
    · apply Subtype.ext
      exact (morphismRestrict_base_coe _ _ _).trans hs)
  refine ⟨V.ι ''ᵁ W, ⟨⟨x, hx⟩, hW, rfl⟩, V.ι_image_le W, ?_⟩
  rw [← image_morphismRestrict_preimage]
  exact (MorphismProperty.arrow_mk_iso_iff (.isomorphisms Scheme)
    (morphismRestrictRestrict f (q ⁻¹ᵁ V) ((q ∣_ V) ⁻¹ᵁ W))).1 hiso

/- English proof (translation)
Introduce `R _ _ _ _ S X π U a b g τ c hπ _ _ _ hU ha _ hτ hc1 hc2 hc x _ _ hinj hsurj V hxV hV`. Establish `hcomm : a ≫ U.hom = b ≫ π`. Rewrite using `[← hτ, ← Category.assoc, ← hc1, ← hc2, Category.assoc, Category.assoc, pullback.condition]`. Take `⟨f, hf1, hf2⟩ : ∃ f : X ⟶ pullback U.hom π, f ≫ pullback.fst _ _ = a ∧ f ≫ pullback.snd _ _ = b` from `⟨pullback.lift a b hcomm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩`. Substitute `hf1` using the available equality.

Establish `hfp : IsProper f` using `IsProper.of_comp f (pullback.fst U.hom π)`. Set `G : pullback U.hom π ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π` to `pullback.lift (pullback.fst _ _ ≫ τ) (pullback.snd _ _) (by rw [Category.assoc, hτ, pullback.condition])`. Establish `hG1 : G ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ` using `pullback.lift_fst _ _ _`. Establish `hG2 : G ≫ pullback.snd _ _ = pullback.snd _ _` using `pullback.lift_snd _ _ _`. Establish `hG : IsPullback G (pullback.fst U.hom π) (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π) τ`.

Use `IsPullback.of_right ?_ hG1 (IsPullback.of_hasPullback _ π).flip` and prove the remaining obligations. Rewrite using `[hG2, hτ]`. Conclude with `(IsPullback.of_hasPullback _ π).flip`. Establish `hfG : f ≫ G = c`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, hG1, hc1, Category.assoc]`. Rewrite using `[Category.assoc, hG2, hc2, hf2]`. Establish `hG'` using `(isPullback_morphismRestrict (pullback.fst U.hom π) V).flip.paste_horiz hG`. Establish `hGe : Etale ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ G)` using `MorphismProperty.of_isPullback (P := @Etale) hG'.flip hV`. Establish `hfe : Etale (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ V))`.

Establish `: Etale (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ V) ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ G)`. Rewrite using `[morphismRestrict_ι_assoc, hfG]`. Use `infer_instance`. Conclude with `Etale.of_comp _ ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ G)`. Take `⟨W, hxW, hWV, hiso⟩` from `exists_isIso_restrict' f (pullback.fst U.hom π) x V hxV (by`.

Introduce `Ω _ p p' h1 h2`. Use `hinj Ω p p' h1 ?_ ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, h2, Category.assoc]`. Rewrite using `[← hf2, ← Category.assoc, h2, Category.assoc]) (by`. Introduce `y hy`.

Set `K` to `(pullback U.hom π).residueField y`. Set `w : Sp (AlgebraicClosure K) ⟶ pullback U.hom π` to `Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ (pullback U.hom π).fromSpecResidueField y`. Set `t : Sp (AlgebraicClosure K)` to `closedPoint (AlgebraicClosure K)`. Establish `hw : w t = y`. Establish `: w t ∈ Set.range ((pullback U.hom π).fromSpecResidueField y)` using `⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩`.

Rewrite `this` using `[Scheme.range_fromSpecResidueField]`. Then use the resulting hypothesis. Take `⟨p, hp1, hp2⟩` from `hsurj (AlgebraicClosure K) (w ≫ pullback.fst _ _) (w ≫ pullback.snd _ _) (by rw [range_pt _ t, Scheme.Hom.comp_apply, hw, hy]) (by simp [pullback.condition])`. Establish `: p ≫ f = w`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hp1]`.

Rewrite using `[Category.assoc, hf2, hp2]`. Conclude with `⟨p t, by rw [← Scheme.Hom.comp_apply, this, hw]⟩)`. Use `⟨W, hxW, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← U.left.homOfLE_ι hWV, Category.assoc] infer_instance`. Establish `P1` using `(isPullback_morphismRestrict (pullback.fst U.hom π) W).paste_vert (IsPullback.of_hasPullback U.hom π)`.

Establish `P0 : IsPullback (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ W) ≫ pullback.fst U.hom π ∣_ W) (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ W) ≫ (pullback.fst U.hom π ⁻¹ᵁ W).ι ≫ pullback.snd U.hom π) (W.ι ≫ U.hom) π` using `P1.of_iso (asIso (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ W))).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp only [Iso.symm_hom, asIso_inv, IsIso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]) (by simp) (by simp)`. Rewrite `P0` using `[morphismRestrict_ι_assoc, hf2, ← morphismRestrict_comp]`. Conclude with `P0`.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ V : U.left.Opens, x ∈ V → Etale (V.ι ≫ τ) → ∃ V : U.left.Opens, x ∈ V ∧ Etale (V.ι ≫ τ) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ b) (V.ι ≫ U.hom) π := by
  intro R _ _ _ _ S X π U a b g τ c hπ _ _ _ hU ha _ hτ hc1 hc2 hc x _ _ hinj hsurj V hxV hV
  have hcomm : a ≫ U.hom = b ≫ π := by
    rw [← hτ, ← Category.assoc, ← hc1, ← hc2, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨f, hf1, hf2⟩ : ∃ f : X ⟶ pullback U.hom π, f ≫ pullback.fst _ _ = a ∧ f ≫ pullback.snd _ _ = b :=
    ⟨pullback.lift a b hcomm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  subst hf1
  have hfp : IsProper f := IsProper.of_comp f (pullback.fst U.hom π)
  let G : pullback U.hom π ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π :=
    pullback.lift (pullback.fst _ _ ≫ τ) (pullback.snd _ _) (by rw [Category.assoc, hτ, pullback.condition])
  have hG1 : G ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ := pullback.lift_fst _ _ _
  have hG2 : G ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hG : IsPullback G (pullback.fst U.hom π) (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π) τ := by
    refine IsPullback.of_right ?_ hG1 (IsPullback.of_hasPullback _ π).flip
    rw [hG2, hτ]
    exact (IsPullback.of_hasPullback _ π).flip
  have hfG : f ≫ G = c := by
    apply pullback.hom_ext
    · rw [Category.assoc, hG1, hc1, Category.assoc]
    · rw [Category.assoc, hG2, hc2, hf2]
  have hG' := (isPullback_morphismRestrict (pullback.fst U.hom π) V).flip.paste_horiz hG
  have hGe : Etale ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ G) :=
    MorphismProperty.of_isPullback (P := @Etale) hG'.flip hV
  have hfe : Etale (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ V)) := by
    have : Etale (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ V) ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ G) := by
      rw [morphismRestrict_ι_assoc, hfG]; infer_instance
    exact Etale.of_comp _ ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ G)
  obtain ⟨W, hxW, hWV, hiso⟩ := exists_isIso_restrict' f (pullback.fst U.hom π) x V hxV (by
    intro Ω _ p p' h1 h2
    refine hinj Ω p p' h1 ?_ ?_
    · rw [← Category.assoc, h2, Category.assoc]
    · rw [← hf2, ← Category.assoc, h2, Category.assoc]) (by
    intro y hy
    let K := (pullback U.hom π).residueField y
    let w : Sp (AlgebraicClosure K) ⟶ pullback U.hom π :=
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ (pullback U.hom π).fromSpecResidueField y
    let t : Sp (AlgebraicClosure K) := closedPoint (AlgebraicClosure K)
    have hw : w t = y := by
      have : w t ∈ Set.range ((pullback U.hom π).fromSpecResidueField y) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rwa [Scheme.range_fromSpecResidueField] at this
    obtain ⟨p, hp1, hp2⟩ := hsurj (AlgebraicClosure K) (w ≫ pullback.fst _ _) (w ≫ pullback.snd _ _)
      (by rw [range_pt _ t, Scheme.Hom.comp_apply, hw, hy]) (by simp [pullback.condition])
    have : p ≫ f = w := by
      apply pullback.hom_ext
      · rw [Category.assoc, hp1]
      · rw [Category.assoc, hf2, hp2]
    exact ⟨p t, by rw [← Scheme.Hom.comp_apply, this, hw]⟩)
  refine ⟨W, hxW, ?_, ?_⟩
  · rw [← U.left.homOfLE_ι hWV, Category.assoc]
    infer_instance
  · have P1 := (isPullback_morphismRestrict (pullback.fst U.hom π) W).paste_vert (IsPullback.of_hasPullback U.hom π)
    have P0 : IsPullback (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ W) ≫ pullback.fst U.hom π ∣_ W)
        (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ W) ≫ (pullback.fst U.hom π ⁻¹ᵁ W).ι ≫ pullback.snd U.hom π)
        (W.ι ≫ U.hom) π :=
      P1.of_iso (asIso (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ W))).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp only [Iso.symm_hom, asIso_inv, IsIso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id])
        (by simp) (by simp)
    rw [morphismRestrict_ι_assoc, hf2, ← morphismRestrict_comp] at P0
    exact P0

end GlobalTheory.Mum.EtalePull
