import Mathlib

/- English proof (translation)
Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `ha.exists_right_inv`. Take `⟨b, rfl⟩` from `hs c`. Establish `h0 : π (a * b - 1) = 0` using `by rw [map_sub, map_mul, hc, map_one, sub_self]`. Establish `hn : IsNilpotent (a * b - 1)` using `⟨2, by rw [pow_two]; exact hk _ h0⟩`.

Establish `hu : IsUnit (a * b)` using `by simpa using hn.isUnit_add_one`. Conclude with `isUnit_of_mul_isUnit_left hu`.
-/
private lemma UpperTheory.isLocalHom_of_square_zero {A B : Type*} [CommRing A] [CommRing B] (π : A →+* B)
    (hs : Function.Surjective π) (hk : ∀ x, π x = 0 → x * x = 0) : IsLocalHom π := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := ha.exists_right_inv
  obtain ⟨b, rfl⟩ := hs c
  have h0 : π (a * b - 1) = 0 := by rw [map_sub, map_mul, hc, map_one, sub_self]
  have hn : IsNilpotent (a * b - 1) := ⟨2, by rw [pow_two]; exact hk _ h0⟩
  have hu : IsUnit (a * b) := by simpa using hn.isUnit_add_one
  exact isUnit_of_mul_isUnit_left hu

/- English proof (translation)
Apply the tactic sequence `open AlgebraicGeometry CategoryTheory in`. Introduce `X Y f _ s hs p`. Establish `hp : f (s p) = p`. Rewrite using `[← Scheme.Hom.comp_apply, hs]`. Both sides reduce to the same expression.

Establish `hi : Inseparable p (f (s p))` using `Inseparable.of_eq hp.symm`. Establish `hfs : (f.stalkMap (s p)).hom.FormallySmooth`. Rewrite using `[← Scheme.Hom.mem_smoothLocus, f.smoothLocus_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Establish `hft : (f.stalkMap (s p)).hom.EssFiniteType` using `LocallyOfFiniteType.stalkMap f (s p)`.

Use `⟨Y.presheaf.stalk (s p), (X.presheaf.stalkCongr hi).hom ≫ f.stalkMap (s p), s.stalkMap p, Y.fromSpecStalk (s p), ?_, ?_, inferInstance, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mpr hfs`. Conclude with `(RingHom.EssFiniteType.respectsIso.cancel_left_isIso _ _).mpr hft`. Establish `h : Spec.map (X.presheaf.stalkCongr hi).hom ≫ X.fromSpecStalk p = X.fromSpecStalk (f (s p))` using `Scheme.SpecMap_stalkSpecializes_fromSpecStalk hi.specializes'`. Rewrite using `[Spec.map_comp, Category.assoc, h, Scheme.SpecMap_stalkMap_fromSpecStalk]`.

Conclude with `Scheme.SpecMap_stalkMap_fromSpecStalk s`. Introduce `R R' _ π φ v hπ hk hv haveI : IsLocalHom π.hom := UpperTheory.isLocalHom_of_square_zero π.hom hπ hk haveI : IsLocalRing R' := π.hom.domain_isLocalRing`. Establish `hsp : v (IsLocalRing.closedPoint R') ⤳ s p`. Establish `h1 : v (IsLocalRing.closedPoint R') = s (X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R)))`. Establish `h3 : v (Spec.map π (IsLocalRing.closedPoint R)) = s (X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R)))` using `congrArg (fun k : Spec R ⟶ Y => k (IsLocalRing.closedPoint R)) hv`.

Conclude with `(congrArg v (Spec_closedPoint (f := π)).symm).trans h3`. Establish `h2 : X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R)) ⤳ p`. Establish `: X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R)) ∈ Set.range (X.fromSpecStalk p)` using `⟨_, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis. Rewrite using `[h1]`.

Conclude with `h2.map s.continuous`. Use `⟨Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo v, ?_⟩` and prove the remaining obligations. Rewrite using `[Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]`.
-/
theorem UpperTheory.formally_smooth_section_stalk :
    open AlgebraicGeometry CategoryTheory in
        ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [Smooth f] (s : X ⟶ Y), s ≫ f = 𝟙 X → ∀ p : X,
          ∃ (B : CommRingCat.{0}) (α : X.presheaf.stalk p ⟶ B) (σ : B ⟶ X.presheaf.stalk p) (ι : Spec B ⟶ Y),
            α.hom.FormallySmooth ∧ α.hom.EssFiniteType ∧ Mono ι ∧
              ι ≫ f = Spec.map α ≫ X.fromSpecStalk p ∧ Spec.map σ ≫ ι = X.fromSpecStalk p ≫ s ∧
              ∀ (R R' : CommRingCat.{0}) [IsLocalRing R] (π : R' ⟶ R) (φ : X.presheaf.stalk p ⟶ R) (v : Spec R' ⟶ Y),
                Function.Surjective π.hom → (∀ x, π.hom x = 0 → x * x = 0) →
                  Spec.map π ≫ v = Spec.map φ ≫ X.fromSpecStalk p ≫ s → ∃ g : B ⟶ R', v = Spec.map g ≫ ι := by
  open AlgebraicGeometry CategoryTheory in
  intro X Y f _ s hs p
  have hp : f (s p) = p := by
    rw [← Scheme.Hom.comp_apply, hs]; rfl
  have hi : Inseparable p (f (s p)) := Inseparable.of_eq hp.symm
  have hfs : (f.stalkMap (s p)).hom.FormallySmooth := by
    rw [← Scheme.Hom.mem_smoothLocus, f.smoothLocus_eq_top]; trivial
  have hft : (f.stalkMap (s p)).hom.EssFiniteType := LocallyOfFiniteType.stalkMap f (s p)
  refine ⟨Y.presheaf.stalk (s p), (X.presheaf.stalkCongr hi).hom ≫ f.stalkMap (s p),
    s.stalkMap p, Y.fromSpecStalk (s p), ?_, ?_, inferInstance, ?_, ?_, ?_⟩
  · exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mpr hfs
  · exact (RingHom.EssFiniteType.respectsIso.cancel_left_isIso _ _).mpr hft
  · have h : Spec.map (X.presheaf.stalkCongr hi).hom ≫ X.fromSpecStalk p =
        X.fromSpecStalk (f (s p)) :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hi.specializes'
    rw [Spec.map_comp, Category.assoc, h, Scheme.SpecMap_stalkMap_fromSpecStalk]
  · exact Scheme.SpecMap_stalkMap_fromSpecStalk s
  · intro R R' _ π φ v hπ hk hv
    haveI : IsLocalHom π.hom := UpperTheory.isLocalHom_of_square_zero π.hom hπ hk
    haveI : IsLocalRing R' := π.hom.domain_isLocalRing
    have hsp : v (IsLocalRing.closedPoint R') ⤳ s p := by
      have h1 : v (IsLocalRing.closedPoint R') =
          s (X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R))) := by
        have h3 : v (Spec.map π (IsLocalRing.closedPoint R)) =
            s (X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R))) :=
          congrArg (fun k : Spec R ⟶ Y => k (IsLocalRing.closedPoint R)) hv
        exact (congrArg v (Spec_closedPoint (f := π)).symm).trans h3
      have h2 : X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R)) ⤳ p := by
        have : X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R)) ∈
            Set.range (X.fromSpecStalk p) := ⟨_, rfl⟩
        rwa [Scheme.range_fromSpecStalk] at this
      rw [h1]
      exact h2.map s.continuous
    refine ⟨Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo v, ?_⟩
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
