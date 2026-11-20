import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkSpecializes

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RegAtDom

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {X' : Scheme.{0}} {Ω' : Type} [Field Ω']

/- English proof (translation)
Use `show Spec.map (X.presheaf.stalkSpecializes (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ X.fromSpecStalk q = ξ`. Establish `h1` using `Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq`. Establish `h2` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) ξ`. Use `Eq.trans ?_ h2` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg (fun g => Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ g) h1)` and prove the remaining obligations.

Conclude with `(congrArg (fun g => g ≫ X.fromSpecStalk q) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)`.
-/
theorem spec_genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : X) (hq : genPt ξ ⤳ q) :
    Spec.map (CommRingCat.ofHom (genMap ξ ⟨q, hq⟩) : X.presheaf.stalk q ⟶ _) ≫ X.fromSpecStalk q = ξ := by
  show Spec.map (X.presheaf.stalkSpecializes (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ X.fromSpecStalk q = ξ
  have h1 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) ξ
  refine Eq.trans ?_ h2
  refine Eq.trans ?_ (congrArg (fun g => Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ g) h1)
  exact (congrArg (fun g => g ≫ X.fromSpecStalk q) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)

/- English proof (translation)
Establish `h1 : (ξ' ≫ f) (IsLocalRing.closedPoint Ω') = (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω')` using `by rw [show ξ' ≫ f = _ from h]`. Establish `h2 : Spec.map (CommRingCat.ofHom i) (IsLocalRing.closedPoint Ω') = IsLocalRing.closedPoint Ω` using `Subsingleton.elim (α := PrimeSpectrum Ω) _ _`. Conclude with `h1.trans (congrArg ξ h2)`.
-/
theorem map_genPt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X}
    {i : Ω →+* Ω'} (h : Dominates ξ' ξ f i) : f (genPt ξ') = genPt ξ := by
  have h1 : (ξ' ≫ f) (IsLocalRing.closedPoint Ω') =
      (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω') := by rw [show ξ' ≫ f = _ from h]
  have h2 : Spec.map (CommRingCat.ofHom i) (IsLocalRing.closedPoint Ω') = IsLocalRing.closedPoint Ω :=
    Subsingleton.elim (α := PrimeSpectrum Ω) _ _
  exact h1.trans (congrArg ξ h2)

/- English proof (translation)
Establish `e : f.stalkMap q ≫ (CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) = (CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) ≫ CommRingCat.ofHom i`. Apply `Spec.map_injective` to reduce the goal to its premises. Establish `h1` using `spec_genMap ξ' q hq`. Establish `h2` using `spec_genMap ξ (f q) hp`. Generalize the expression as in `(CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) = u at h1 ⊢`.

Generalize the expression as in `(CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) = v at h2 ⊢`. Establish `h3` using `Scheme.SpecMap_stalkMap_fromSpecStalk f (x := q)`. Use `(cancel_mono (X.fromSpecStalk (f q))).1 ?_` and prove the remaining obligations. Establish `l : Spec.map (f.stalkMap q ≫ u) ≫ X.fromSpecStalk (f q) = ξ' ≫ f` using `((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans ((congrArg (fun g => Spec.map u ≫ g) h3).trans ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ f) h1)))`. Establish `r : Spec.map (v ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (f q) = Spec.map (CommRingCat.ofHom i) ≫ ξ` using `((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans (congrArg (fun g => Spec.map (CommRingCat.ofHom i) ≫ g) h2)`.

Conclude with `l.trans (Eq.trans h r.symm)`. Conclude with `congrArg (fun g => g.hom s) e`.
-/
theorem genMap_stalkMap {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X}
    {i : Ω →+* Ω'} (h : Dominates ξ' ξ f i) (q : X') (hq : genPt ξ' ⤳ q) (hp : genPt ξ ⤳ f q)
    (s : X.presheaf.stalk (f q)) :
    genMap ξ' ⟨q, hq⟩ ((f.stalkMap q).hom s) = i (genMap ξ ⟨f q, hp⟩ s) := by
  have e : f.stalkMap q ≫ (CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) =
      (CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) ≫ CommRingCat.ofHom i := by
    apply Spec.map_injective
    have h1 := spec_genMap ξ' q hq
    have h2 := spec_genMap ξ (f q) hp
    generalize (CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) = u at h1 ⊢
    generalize (CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) = v at h2 ⊢
    have h3 := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := q)
    refine (cancel_mono (X.fromSpecStalk (f q))).1 ?_
    have l : Spec.map (f.stalkMap q ≫ u) ≫ X.fromSpecStalk (f q) = ξ' ≫ f :=
      ((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans
        ((congrArg (fun g => Spec.map u ≫ g) h3).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ f) h1)))
    have r : Spec.map (v ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (f q) = Spec.map (CommRingCat.ofHom i) ≫ ξ :=
      ((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans
        (congrArg (fun g => Spec.map (CommRingCat.ofHom i) ≫ g) h2)
    exact l.trans (Eq.trans h r.symm)
  exact congrArg (fun g => g.hom s) e

/- English proof (translation)
Introduce `X Ω _ ξ X' Ω' _ ξ' f i hd p'`. Take `⟨q, hq⟩` from `p'`. Establish `hp : genPt ξ ⤳ f q` using `map_genPt hd ▸ hq.map f.continuous`. Use `⟨hp, ?_, fun hg => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨s, rfl⟩`.

Conclude with `⟨(f.stalkMap q).hom s, genMap_stalkMap hd q hq hp s⟩`. Introduce and unpack `_ ⟨s, rfl⟩ ⟨h0, -, t, ht⟩`. Establish `hv` using `genMap_stalkMap hd q hq hp s`. Establish `hone : (f.stalkMap q).hom s * t = 1`. Apply `hg.inj ⟨q, hq⟩` to reduce the goal to its premises.

Rewrite using `[map_mul, map_one, hv, ht]`. Conclude with `mul_inv_cancel₀ h0`. Establish `hu : IsUnit ((f.stalkMap q).hom s)` using `IsUnit.of_mul_eq_one _ hone`. Conclude with `RegAtMono.unitAt_of_isUnit ξ ⟨f q, hp⟩ (isUnit_of_map_unit (f.stalkMap q).hom s hu)`.
-/
theorem regAt_dominates :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type)
      [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), Dominates ξ' ξ f i →
      ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1, (∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧
        (IsCptGen ξ' → ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, unitAt ξ' p' (i a) → unitAt ξ ⟨f p'.1, h⟩ a) := by
  intro X Ω _ ξ X' Ω' _ ξ' f i hd p'
  obtain ⟨q, hq⟩ := p'
  have hp : genPt ξ ⤳ f q := map_genPt hd ▸ hq.map f.continuous
  refine ⟨hp, ?_, fun hg => ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨(f.stalkMap q).hom s, genMap_stalkMap hd q hq hp s⟩
  · rintro _ ⟨s, rfl⟩ ⟨h0, -, t, ht⟩
    have hv := genMap_stalkMap hd q hq hp s
    have hone : (f.stalkMap q).hom s * t = 1 := by
      apply hg.inj ⟨q, hq⟩
      rw [map_mul, map_one, hv, ht]
      exact mul_inv_cancel₀ h0
    have hu : IsUnit ((f.stalkMap q).hom s) := IsUnit.of_mul_eq_one _ hone
    exact RegAtMono.unitAt_of_isUnit ξ ⟨f q, hp⟩ (isUnit_of_map_unit (f.stalkMap q).hom s hu)

end GlobalTheory.CompanionTheory.Ar.RegAtDom
