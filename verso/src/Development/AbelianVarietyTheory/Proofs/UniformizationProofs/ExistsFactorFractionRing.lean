import Mathlib

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.AffineFactorExists

/- English proof (translation)
Take `⟨i, z, hz⟩` from `X.affineCover.exists_eq (x default)`. Set `ι : Spec _ ⟶ X` to `X.affineCover.f i`. Establish `hι : IsOpenImmersion ι` using `inferInstanceAs (IsOpenImmersion (X.affineCover.f i))`. Establish `hr : Set.range x ⊆ Set.range ι`. Introduce and unpack `_ ⟨p, rfl⟩`.

Take `rfl : p = default` from `Subsingleton.elim _ _`. Conclude with `⟨z, hz⟩`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (IsOpenImmersion.lift ι x hr)`. Conclude with `⟨_, ι, hι, φ, by rw [hφ, IsOpenImmersion.lift_fac]⟩`.
-/
theorem exists_affine_factor {F : Type} [Field F] {X : Scheme.{0}}
    (x : Spec (CommRingCat.of F) ⟶ X) :
    ∃ (A : CommRingCat.{0}) (ι : Spec A ⟶ X) (_ : IsOpenImmersion ι) (φ : A ⟶ CommRingCat.of F),
      Spec.map φ ≫ ι = x := by
  obtain ⟨i, z, hz⟩ := X.affineCover.exists_eq (x default)
  let ι : Spec _ ⟶ X := X.affineCover.f i
  have hι : IsOpenImmersion ι := inferInstanceAs (IsOpenImmersion (X.affineCover.f i))
  have hr : Set.range x ⊆ Set.range ι := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = default := Subsingleton.elim _ _
    exact ⟨z, hz⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift ι x hr)
  exact ⟨_, ι, hι, φ, by rw [hφ, IsOpenImmersion.lift_fac]⟩

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap W F)` using `Subtype.val_injective`. Set `j : FractionRing W →+* F` to `IsFractionRing.lift hinj`. Establish `hj : ∀ w : W, j (algebraMap W (FractionRing W) w) = w` using `fun w => IsFractionRing.lift_algebraMap hinj w`. Establish `hmem : ∀ a : A, φ a ∈ j.range`. Introduce `a`.

Establish `ha : a ∈ Algebra.adjoin V s` using `hs ▸ Algebra.mem_top`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem a ha`. Take `⟨u, hu, v, hv, hv0, e⟩` from `h a ha`. Use `⟨algebraMap W _ ⟨u, hu⟩ / algebraMap W _ ⟨v, hv⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_div₀, hj, hj, div_eq_iff hv0, e]`. Consider the case `algebraMap r`. Conclude with `⟨algebraMap W _ (algebraMap V W r), by rw [hj, AlgHom.commutes]; rfl⟩`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`.

Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `mul_mem ha hb`. Set `e : FractionRing W ≃+* j.range` to `RingEquiv.ofBijective j.rangeRestrict ⟨j.rangeRestrict.injective, j.rangeRestrict_surjective⟩`. Use `⟨j, e.symm.toRingHom.comp (φ.toRingHom.codRestrict j.range hmem), RingHom.ext hj, ?_⟩` and prove the remaining obligations. Use extensionality with `a`.

Conclude with `congrArg Subtype.val (e.apply_symm_apply ⟨φ a, hmem a⟩)`.
-/
theorem exists_factor_fractionRing {V A F : Type} [CommRing V] [CommRing A] [Field F]
    [Algebra V A] [Algebra V F] (φ : A →ₐ[V] F) (s : Set A) (hs : Algebra.adjoin V s = ⊤)
    (W : Subalgebra V F)
    (h : ∀ a ∈ s, ∃ u ∈ W, ∃ v ∈ W, v ≠ (0 : F) ∧ φ a * v = u) :
    ∃ (j : FractionRing W →+* F) (φ' : A →+* FractionRing W),
      j.comp (algebraMap W (FractionRing W)) = algebraMap W F ∧ j.comp φ' = φ.toRingHom := by
  have hinj : Function.Injective (algebraMap W F) := Subtype.val_injective
  let j : FractionRing W →+* F := IsFractionRing.lift hinj
  have hj : ∀ w : W, j (algebraMap W (FractionRing W) w) = w := fun w =>
    IsFractionRing.lift_algebraMap hinj w
  have hmem : ∀ a : A, φ a ∈ j.range := by
    intro a
    have ha : a ∈ Algebra.adjoin V s := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨u, hu, v, hv, hv0, e⟩ := h a ha
      refine ⟨algebraMap W _ ⟨u, hu⟩ / algebraMap W _ ⟨v, hv⟩, ?_⟩
      rw [map_div₀, hj, hj, div_eq_iff hv0, e]
    | algebraMap r =>
      exact ⟨algebraMap W _ (algebraMap V W r), by rw [hj, AlgHom.commutes]; rfl⟩
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let e : FractionRing W ≃+* j.range :=
    RingEquiv.ofBijective j.rangeRestrict
      ⟨j.rangeRestrict.injective, j.rangeRestrict_surjective⟩
  refine ⟨j, e.symm.toRingHom.comp (φ.toRingHom.codRestrict j.range hmem), RingHom.ext hj, ?_⟩
  ext a
  exact congrArg Subtype.val (e.apply_symm_apply ⟨φ a, hmem a⟩)

/- English proof (translation)
Take `⟨A, ι, hι, φ, hφ⟩` from `exists_affine_factor x`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (ι ≫ f)`. Establish `hft : ψ.hom.FiniteType`. Rewrite using `[← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hψ]`. Use `infer_instance`.

Establish `hcomp : ψ ≫ φ = CommRingCat.ofHom (algebraMap V F)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hψ, ← Category.assoc, hφ, hx]`. Use `letI : Algebra V A := ψ.hom.toAlgebra`. Establish `hft' : Algebra.FiniteType V A` using `hft`.

Take `⟨s, hs⟩` from `hft'.out`. Set `φa : A →ₐ[V] F` to `{ φ.hom with commutes' := fun r => congrArg (fun g => g.hom r) hcomp }`. Use `⟨s.image φ.hom, fun W hW ht => ?_⟩` and prove the remaining obligations. Take `⟨j, φ', hj, hφ'⟩` from `exists_factor_fractionRing φa s hs W (fun a ha => ht _ (Finset.mem_image_of_mem _ ha))`. Establish `hE : ValuativeCriterion.Existence f`.

Establish `: UniversallyClosed f` using `inferInstance`. Rewrite `this` using `[UniversallyClosed.eq_valuativeCriterion]`. Conclude with `this.1`. Establish `hring : ψ ≫ CommRingCat.ofHom φ' = CommRingCat.ofHom (algebraMap V W) ≫ CommRingCat.ofHom (algebraMap W (FractionRing W))`. Use extensionality with `r`.

Apply `j.injective` to reduce the goal to its premises. Establish `h1` using `RingHom.congr_fun hφ' (ψ.hom r)`. Establish `h2` using `RingHom.congr_fun hj (algebraMap V W r)`. Conclude with `(h1.trans (φa.commutes r)).trans h2.symm`. Establish `w : (Spec.map (CommRingCat.ofHom φ') ≫ ι) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap W (FractionRing W))) ≫ Spec.map (CommRingCat.ofHom (algebraMap V W))`.

Rewrite using `[Category.assoc, ← hψ, ← Spec.map_comp, ← Spec.map_comp, hring]`. Take `⟨l, hl₁, hl₂⟩` from `(hE { R := W, K := FractionRing W, commSq := ⟨w⟩, .. }).exists_lift`. Simplify using `only at hl₁ hl₂`. Use `⟨l, hl₂, ?_⟩` and prove the remaining obligations. Establish `e₁ : CommRingCat.ofHom (algebraMap W F) = CommRingCat.ofHom (algebraMap W (FractionRing W)) ≫ CommRingCat.ofHom j`.

Rewrite using `[← hj]`. Both sides reduce to the same expression. Establish `e₂ : φ = CommRingCat.ofHom φ' ≫ CommRingCat.ofHom j`. Use extensionality with `a`. Conclude with `(RingHom.congr_fun hφ' a).symm`.

Rewrite using `[e₁, Spec.map_comp, Category.assoc, hl₁, ← Category.assoc, ← Spec.map_comp, ← e₂, hφ]`.
-/
theorem exists_finset_extends (V F : Type) [CommRing V] [Field F] [Algebra V F]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f]
    (x : Spec (CommRingCat.of F) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V F))) :
    ∃ t : Finset F, ∀ W : Subalgebra V F, ValuationRing W →
      (∀ x ∈ t, ∃ a ∈ W, ∃ b ∈ W, b ≠ (0 : F) ∧ x * b = a) →
      ∃ y : Spec (CommRingCat.of W) ⟶ X,
        y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V W)) ∧
        Spec.map (CommRingCat.ofHom (algebraMap W F)) ≫ y = x := by
  classical
  obtain ⟨A, ι, hι, φ, hφ⟩ := exists_affine_factor x
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (ι ≫ f)
  have hft : ψ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hψ]
    infer_instance
  have hcomp : ψ ≫ φ = CommRingCat.ofHom (algebraMap V F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, ← Category.assoc, hφ, hx]
  letI : Algebra V A := ψ.hom.toAlgebra
  have hft' : Algebra.FiniteType V A := hft
  obtain ⟨s, hs⟩ := hft'.out
  let φa : A →ₐ[V] F :=
    { φ.hom with commutes' := fun r => congrArg (fun g => g.hom r) hcomp }
  refine ⟨s.image φ.hom, fun W hW ht => ?_⟩
  obtain ⟨j, φ', hj, hφ'⟩ := exists_factor_fractionRing φa s hs W
    (fun a ha => ht _ (Finset.mem_image_of_mem _ ha))
  have hE : ValuativeCriterion.Existence f := by
    have : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at this
    exact this.1
  have hring : ψ ≫ CommRingCat.ofHom φ' =
      CommRingCat.ofHom (algebraMap V W) ≫
        CommRingCat.ofHom (algebraMap W (FractionRing W)) := by
    ext r
    apply j.injective
    have h1 := RingHom.congr_fun hφ' (ψ.hom r)
    have h2 := RingHom.congr_fun hj (algebraMap V W r)
    exact (h1.trans (φa.commutes r)).trans h2.symm
  have w : (Spec.map (CommRingCat.ofHom φ') ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap W (FractionRing W))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V W)) := by
    rw [Category.assoc, ← hψ, ← Spec.map_comp, ← Spec.map_comp, hring]
  obtain ⟨l, hl₁, hl₂⟩ :=
    (hE { R := W, K := FractionRing W, commSq := ⟨w⟩, .. }).exists_lift
  dsimp only at hl₁ hl₂
  refine ⟨l, hl₂, ?_⟩
  have e₁ : CommRingCat.ofHom (algebraMap W F) =
      CommRingCat.ofHom (algebraMap W (FractionRing W)) ≫ CommRingCat.ofHom j := by
    rw [← hj]; rfl
  have e₂ : φ = CommRingCat.ofHom φ' ≫ CommRingCat.ofHom j := by
    ext a
    exact (RingHom.congr_fun hφ' a).symm
  rw [e₁, Spec.map_comp, Category.assoc, hl₁, ← Category.assoc, ← Spec.map_comp, ← e₂, hφ]

end GlobalTheory.AffineFactorExists
